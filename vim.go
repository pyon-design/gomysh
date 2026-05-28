/*
* Last Changed: 2026-05-16 Sat 15:26:37
*/

package main

import (
	"bufio"
	"bytes"
	"fmt"
	"io"
	"os"
	"strings"
	"unicode/utf8"

	"golang.org/x/term"
)

type VimMode int

const (
	VimNormalMode VimMode = iota
	VimInsertMode
	VimCommandMode
)

type VimEditor struct {
	filePath    string
	lines       [][]rune
	cx          int
	cy          int
	rowOffset   int
	colOffset   int
	screenRows  int
	screenCols  int
	mode        VimMode
	cmdline     []rune
	status      string
	modified    bool
	quit        bool
	forceQuit   bool
	lastWasD    bool
	lastWasZ    bool
	origTerm    *term.State
}

func builtinVIM(args []string, stdin io.Reader, stdout, stderr io.Writer) int {
	_ = stdin

	fd := int(os.Stdin.Fd())
	if !term.IsTerminal(fd) {
		fmt.Fprintln(stderr, "vim: stdin is not a terminal")
		return 1
	}

	path := ""
	if len(args) >= 2 {
		path = args[1]
	}
	if len(args) > 2 {
		fmt.Fprintln(stderr, "vim: usage: vim [FILE]")
		return 1
	}

	shellState, err := term.GetState(fd)
	if err == nil {
		_ = term.Restore(fd, shellState)
	}

	editor, err := NewVimEditor(path, shellState)
	if err != nil {
		fmt.Fprintf(stderr, "vim: %v\n", err)
		return 1
	}

	status, err := editor.Run()
	if err != nil {
		fmt.Fprintf(stderr, "vim: %v\n", err)
		return 1
	}
	return status
}

func NewVimEditor(path string, orig *term.State) (*VimEditor, error) {
	cols, rows, err := term.GetSize(int(os.Stdout.Fd()))
	if err != nil || cols <= 0 || rows <= 0 {
		cols, rows = 80, 24
	}

	ve := &VimEditor{
		filePath:   path,
		screenRows: rows,
		screenCols: cols,
		mode:       VimNormalMode,
		origTerm:   orig,
		status:     "-- NORMAL --",
	}

	if path == "" {
		ve.lines = [][]rune{[]rune{}}
		return ve, nil
	}

	data, err := os.ReadFile(path)
	if err != nil {
		if os.IsNotExist(err) {
			ve.lines = [][]rune{[]rune{}}
			ve.status = fmt.Sprintf("\"%s\" [New File]", path)
			return ve, nil
		}
		return nil, err
	}

	text := strings.ReplaceAll(string(data), "\r\n", "\n")
	parts := strings.Split(text, "\n")
	if len(parts) == 0 {
		parts = []string{""}
	}
	if len(parts) > 1 && parts[len(parts)-1] == "" {
		parts = parts[:len(parts)-1]
	}
	ve.lines = make([][]rune, 0, len(parts))
	for _, p := range parts {
		ve.lines = append(ve.lines, []rune(p))
	}
	if len(ve.lines) == 0 {
		ve.lines = [][]rune{[]rune{}}
	}
	ve.status = fmt.Sprintf("\"%s\" %dL", path, len(ve.lines))
	return ve, nil
}

func (v *VimEditor) Run() (int, error) {
	fd := int(os.Stdin.Fd())

	oldState, err := term.MakeRaw(fd)
	if err != nil {
		return 1, err
	}
	defer func() {
		_ = term.Restore(fd, oldState)
		if v.origTerm != nil {
			_ = term.Restore(fd, v.origTerm)
		}
		fmt.Fprint(os.Stdout, "\x1b[2J\x1b[H")
	}()

	if err := v.refreshScreen(); err != nil {
		return 1, err
	}

	for !v.quit {
		key, err := readKey(os.Stdin)
		if err != nil {
			if err == io.EOF {
				break
			}
			return 1, err
		}
		if err := v.handleKey(key); err != nil {
			return 1, err
		}
		if err := v.refreshScreen(); err != nil {
			return 1, err
		}
	}

	return 0, nil
}

func (v *VimEditor) handleKey(key []byte) error {
	v.lastWasD = false
	v.lastWasZ = false

	switch v.mode {
	case VimInsertMode:
		return v.handleInsertKey(key)
	case VimCommandMode:
		return v.handleCommandKey(key)
	default:
		return v.handleNormalKey(key)
	}
}

func (v *VimEditor) handleInsertKey(key []byte) error {
	switch {
	case len(key) == 1 && key[0] == 0x1b:
		v.mode = VimNormalMode
		v.status = "-- NORMAL --"
	case len(key) == 1 && (key[0] == '\r' || key[0] == '\n'):
		v.insertNewLine()
	case len(key) == 1 && (key[0] == 0x7f || key[0] == 0x08):
		v.backspace()
	case len(key) == 3 && key[0] == 0x1b && key[1] == '[' && key[2] == 'A':
		v.moveUp()
	case len(key) == 3 && key[0] == 0x1b && key[1] == '[' && key[2] == 'B':
		v.moveDown()
	case len(key) == 3 && key[0] == 0x1b && key[1] == '[' && key[2] == 'C':
		v.moveRight()
	case len(key) == 3 && key[0] == 0x1b && key[1] == '[' && key[2] == 'D':
		v.moveLeft()
	case len(key) == 1 && key[0] >= 0x20:
		v.insertRune(rune(key[0]))
	default:
		if len(key) == 1 && key[0] < utf8.RuneSelf && key[0] >= 0x20 {
			v.insertRune(rune(key[0]))
		}
	}
	return nil
}

func (v *VimEditor) handleCommandKey(key []byte) error {
	switch {
	case len(key) == 1 && key[0] == 0x1b:
		v.mode = VimNormalMode
		v.cmdline = nil
		v.status = "-- NORMAL --"
	case len(key) == 1 && (key[0] == 0x7f || key[0] == 0x08):
		if len(v.cmdline) > 0 {
			v.cmdline = v.cmdline[:len(v.cmdline)-1]
		}
	case len(key) == 1 && (key[0] == '\r' || key[0] == '\n'):
		return v.execCommandLine(string(v.cmdline))
	case len(key) == 1 && key[0] >= 0x20 && key[0] <= 0x7e:
		v.cmdline = append(v.cmdline, rune(key[0]))
	}
	return nil
}

func (v *VimEditor) handleNormalKey(key []byte) error {
	switch {
	case len(key) == 1 && key[0] == ':':
		v.mode = VimCommandMode
		v.cmdline = nil
		return nil
	case len(key) == 1 && key[0] == 'i':
		v.mode = VimInsertMode
		v.status = "-- INSERT --"
	case len(key) == 1 && key[0] == 'a':
		if v.cx < len(v.currentLine()) {
			v.cx++
		}
		v.mode = VimInsertMode
		v.status = "-- INSERT --"
	case len(key) == 1 && key[0] == 'o':
		v.openBelow()
		v.mode = VimInsertMode
		v.status = "-- INSERT --"
	case len(key) == 1 && key[0] == 'h':
		v.moveLeft()
	case len(key) == 1 && key[0] == 'j':
		v.moveDown()
	case len(key) == 1 && key[0] == 'k':
		v.moveUp()
	case len(key) == 1 && key[0] == 'l':
		v.moveRight()
	case len(key) == 3 && key[0] == 0x1b && key[1] == '[' && key[2] == 'A':
		v.moveUp()
	case len(key) == 3 && key[0] == 0x1b && key[1] == '[' && key[2] == 'B':
		v.moveDown()
	case len(key) == 3 && key[0] == 0x1b && key[1] == '[' && key[2] == 'C':
		v.moveRight()
	case len(key) == 3 && key[0] == 0x1b && key[1] == '[' && key[2] == 'D':
		v.moveLeft()
	case len(key) == 1 && key[0] == '0':
		v.cx = 0
	case len(key) == 1 && key[0] == '$':
		v.cx = len(v.currentLine())
	case len(key) == 1 && key[0] == 'x':
		v.deleteRune()
	case len(key) == 1 && key[0] == 'd':
		if v.lastWasD {
			v.deleteLine()
		} else {
			v.lastWasD = true
			v.status = "d"
		}
	case len(key) == 1 && key[0] == 'Z':
		if v.lastWasZ {
			if err := v.save(); err != nil {
				v.status = err.Error()
			} else {
				v.quit = true
			}
		} else {
			v.lastWasZ = true
			v.status = "Z"
		}
	}
	return nil
}

func (v *VimEditor) execCommandLine(cmd string) error {
	cmd = strings.TrimSpace(cmd)
	v.cmdline = nil
	v.mode = VimNormalMode

	switch cmd {
	case "q":
		if v.modified {
			v.status = "No write since last change (add ! to override)"
			return nil
		}
		v.quit = true
	case "q!":
		v.quit = true
	case "w":
		if err := v.save(); err != nil {
			v.status = err.Error()
		}
	case "wq", "x":
		if err := v.save(); err != nil {
			v.status = err.Error()
		} else {
			v.quit = true
		}
	default:
		v.status = "Not an editor command: " + cmd
	}
	return nil
}

func (v *VimEditor) save() error {
	if v.filePath == "" {
		v.status = "No file name"
		return nil
	}

	var b bytes.Buffer
	for i, line := range v.lines {
		b.WriteString(string(line))
		if i != len(v.lines)-1 {
			b.WriteByte('\n')
		}
	}

	if err := os.WriteFile(v.filePath, b.Bytes(), 0644); err != nil {
		return err
	}
	v.modified = false
	v.status = fmt.Sprintf("\"%s\" %dL written", v.filePath, len(v.lines))
	return nil
}

func (v *VimEditor) currentLine() []rune {
	if v.cy < 0 {
		v.cy = 0
	}
	if v.cy >= len(v.lines) {
		v.cy = len(v.lines) - 1
	}
	return v.lines[v.cy]
}

func (v *VimEditor) setCurrentLine(line []rune) {
	v.lines[v.cy] = line
}

func (v *VimEditor) insertRune(r rune) {
	line := v.currentLine()
	if v.cx < 0 {
		v.cx = 0
	}
	if v.cx > len(line) {
		v.cx = len(line)
	}
	line = append(line[:v.cx], append([]rune{r}, line[v.cx:]...)...)
	v.setCurrentLine(line)
	v.cx++
	v.modified = true
}

func (v *VimEditor) backspace() {
	if v.cx > 0 {
		line := v.currentLine()
		line = append(line[:v.cx-1], line[v.cx:]...)
		v.setCurrentLine(line)
		v.cx--
		v.modified = true
		return
	}
	if v.cy > 0 {
		prev := v.lines[v.cy-1]
		cur := v.lines[v.cy]
		pos := len(prev)
		v.lines[v.cy-1] = append(prev, cur...)
		v.lines = append(v.lines[:v.cy], v.lines[v.cy+1:]...)
		v.cy--
		v.cx = pos
		v.modified = true
	}
}

func (v *VimEditor) insertNewLine() {
	line := v.currentLine()
	left := append([]rune(nil), line[:v.cx]...)
	right := append([]rune(nil), line[v.cx:]...)
	v.lines[v.cy] = left
	idx := v.cy + 1
	v.lines = append(v.lines[:idx], append([][]rune{right}, v.lines[idx:]...)...)
	v.cy++
	v.cx = 0
	v.modified = true
}

func (v *VimEditor) openBelow() {
	idx := v.cy + 1
	v.lines = append(v.lines[:idx], append([][]rune{[]rune{}}, v.lines[idx:]...)...)
	v.cy++
	v.cx = 0
	v.modified = true
}

func (v *VimEditor) deleteRune() {
	line := v.currentLine()
	if v.cx >= len(line) {
		return
	}
	line = append(line[:v.cx], line[v.cx+1:]...)
	v.setCurrentLine(line)
	v.modified = true
}

func (v *VimEditor) deleteLine() {
	if len(v.lines) == 1 {
		v.lines[0] = []rune{}
		v.cx = 0
		v.modified = true
		return
	}
	v.lines = append(v.lines[:v.cy], v.lines[v.cy+1:]...)
	if v.cy >= len(v.lines) {
		v.cy = len(v.lines) - 1
	}
	if v.cx > len(v.currentLine()) {
		v.cx = len(v.currentLine())
	}
	v.modified = true
	v.status = "-- NORMAL --"
}

func (v *VimEditor) moveLeft() {
	if v.cx > 0 {
		v.cx--
	}
}

func (v *VimEditor) moveRight() {
	if v.cx < len(v.currentLine()) {
		v.cx++
	}
}

func (v *VimEditor) moveUp() {
	if v.cy > 0 {
		v.cy--
	}
	if v.cx > len(v.currentLine()) {
		v.cx = len(v.currentLine())
	}
}

func (v *VimEditor) moveDown() {
	if v.cy < len(v.lines)-1 {
		v.cy++
	}
	if v.cx > len(v.currentLine()) {
		v.cx = len(v.currentLine())
	}
}

func (v *VimEditor) scroll() {
	if v.cy < v.rowOffset {
		v.rowOffset = v.cy
	}
	if v.cy >= v.rowOffset+v.screenRows-2 {
		v.rowOffset = v.cy - (v.screenRows - 3)
	}
	if v.cx < v.colOffset {
		v.colOffset = v.cx
	}
	if v.cx >= v.colOffset+v.screenCols {
		v.colOffset = v.cx - v.screenCols + 1
	}
	if v.rowOffset < 0 {
		v.rowOffset = 0
	}
	if v.colOffset < 0 {
		v.colOffset = 0
	}
}

func (v *VimEditor) drawRows(b *bytes.Buffer) {
	usableRows := v.screenRows - 2
	for y := 0; y < usableRows; y++ {
		fileRow := v.rowOffset + y
		b.WriteString("\x1b[K")
		if fileRow < len(v.lines) {
			line := v.lines[fileRow]
			if v.colOffset < len(line) {
				part := line[v.colOffset:]
				if len(part) > v.screenCols {
					part = part[:v.screenCols]
				}
				b.WriteString(string(part))
			}
		} else {
			b.WriteString("~")
		}
		b.WriteString("\r\n")
	}
}

func (v *VimEditor) drawStatusBar(b *bytes.Buffer) {
	mode := "NORMAL"
	switch v.mode {
	case VimInsertMode:
		mode = "INSERT"
	case VimCommandMode:
		mode = "COMMAND"
	}

	name := v.filePath
	if name == "" {
		name = "[No Name]"
	}
	mod := ""
	if v.modified {
		mod = " [+]"
	}
	left := fmt.Sprintf(" %s - %d lines%s ", name, len(v.lines), mod)
	right := fmt.Sprintf(" %s  %d,%d ", mode, v.cy+1, v.cx+1)

	if len([]rune(left))+len([]rune(right)) > v.screenCols {
		rs := []rune(left)
		if len(rs) > v.screenCols-len([]rune(right)) {
			rs = rs[:v.screenCols-len([]rune(right))]
		}
		left = string(rs)
	}
	spaces := v.screenCols - len([]rune(left)) - len([]rune(right))
	if spaces < 1 {
		spaces = 1
	}

	b.WriteString("\x1b[7m")
	b.WriteString(left)
	b.WriteString(strings.Repeat(" ", spaces))
	b.WriteString(right)
	b.WriteString("\x1b[m")
	b.WriteString("\r\n")
}

func (v *VimEditor) drawMessageBar(b *bytes.Buffer) {
	b.WriteString("\x1b[K")
	if v.mode == VimCommandMode {
		b.WriteString(":")
		b.WriteString(string(v.cmdline))
	} else {
		msg := v.status
		rs := []rune(msg)
		if len(rs) > v.screenCols {
			rs = rs[:v.screenCols]
		}
		b.WriteString(string(rs))
	}
}

func (v *VimEditor) refreshScreen() error {
	cols, rows, err := term.GetSize(int(os.Stdout.Fd()))
	if err == nil && cols > 0 && rows > 0 {
		v.screenCols = cols
		v.screenRows = rows
	}

	v.scroll()

	var b bytes.Buffer
	b.WriteString("\x1b[?25l")
	b.WriteString("\x1b[H")
	v.drawRows(&b)
	v.drawStatusBar(&b)
	v.drawMessageBar(&b)

	cursorRow := (v.cy - v.rowOffset) + 1
	cursorCol := (v.cx - v.colOffset) + 1
	if v.mode == VimCommandMode {
		cursorRow = v.screenRows
		cursorCol = len([]rune(v.cmdline)) + 2
	}

	if cursorRow < 1 {
		cursorRow = 1
	}
	if cursorCol < 1 {
		cursorCol = 1
	}

	b.WriteString(fmt.Sprintf("\x1b[%d;%dH", cursorRow, cursorCol))
	b.WriteString("\x1b[?25h")

	_, err = os.Stdout.Write(b.Bytes())
	return err
}

func readLineFromReader(r io.Reader) (string, error) {
	br := bufio.NewReader(r)
	s, err := br.ReadString('\n')
	if err != nil && err != io.EOF {
		return "", err
	}
	return strings.TrimRight(s, "\r\n"), nil
}
