/*
 * Last Changed: 2026-05-13 Wed 12:53:42
 */
package main

import (
	"archive/tar"
	"bufio"
	"bytes"
	"compress/gzip"
	"crypto/md5"
	"crypto/sha256"
	"crypto/sha512"
	"encoding/hex"
	"fmt"
	"io"
	"hash"
	"math"
	"net"
	"net/http"
	"os"
	"os/exec"
	"os/user"
	"path/filepath"
	"sort"
	"strconv"
	"strings"
	"sync"
	"time"
	"unicode"
	"unicode/utf8"

	"golang.org/x/term"
)

const (
	Version = "0.3" // -ldflags="-X main.Version=1.2.3"

	colorOff    = "\x1b[0m"
	colorRed    = "\x1b[31m"
	colorGreen  = "\x1b[32m"
	colorYellow = "\x1b[33m"
	colorBlue   = "\x1b[34m"
	colorDir    = "\x1b[01;34m"
	colorToday  = "\x1b[32m"

	inputPrompt = "$ "
)

type Editor struct {
	buf    []rune
	cursor int
	yank   []rune
}

func (e *Editor) insertRune(r rune) {
	if e.cursor == len(e.buf) {
		e.buf = append(e.buf, r)
		e.cursor++
		return
	}
	e.buf = append(e.buf[:e.cursor], append([]rune{r}, e.buf[e.cursor:]...)...)
	e.cursor++
}

func (e *Editor) backspace() {
	if e.cursor == 0 {
		return
	}
	e.buf = append(e.buf[:e.cursor-1], e.buf[e.cursor:]...)
	e.cursor--
}

func (e *Editor) moveHome() { e.cursor = 0 }
func (e *Editor) moveEnd()  { e.cursor = len(e.buf) }

func (e *Editor) moveLeft() {
	if e.cursor > 0 {
		e.cursor--
	}
}

func (e *Editor) moveRight() {
	if e.cursor < len(e.buf) {
		e.cursor++
	}
}

func (e *Editor) clear() {
	e.buf = nil
	e.cursor = 0
}

func (e *Editor) line() string {
	return string(e.buf)
}

func (e *Editor) replaceRange(start, end int, s string) {
	if start < 0 {
		start = 0
	}
	if end < start {
		end = start
	}
	if end > len(e.buf) {
		end = len(e.buf)
	}

	repl := []rune(s)
	newBuf := make([]rune, 0, len(e.buf)-(end-start)+len(repl))
	newBuf = append(newBuf, e.buf[:start]...)
	newBuf = append(newBuf, repl...)
	newBuf = append(newBuf, e.buf[end:]...)
	e.buf = newBuf
	e.cursor = start + len(repl)
}

func (e *Editor) setLine(s string) {
	e.buf = []rune(s)
	e.cursor = len(e.buf)
}

func (e *Editor) killToStart() {
	if e.cursor <= 0 {
		e.yank = nil
		return
	}
	e.yank = append([]rune(nil), e.buf[:e.cursor]...)
	e.buf = append([]rune(nil), e.buf[e.cursor:]...)
	e.cursor = 0
}

func (e *Editor) killToEnd() {
	if e.cursor >= len(e.buf) {
		e.yank = nil
		return
	}
	e.yank = append([]rune(nil), e.buf[e.cursor:]...)
	e.buf = append([]rune(nil), e.buf[:e.cursor]...)
}

func (e *Editor) killPrevWord() {
	if e.cursor <= 0 {
		e.yank = nil
		return
	}

	start := e.cursor

	for start > 0 && unicode.IsSpace(e.buf[start-1]) {
		start--
	}
	for start > 0 && !unicode.IsSpace(e.buf[start-1]) {
		start--
	}

	e.yank = append([]rune(nil), e.buf[start:e.cursor]...)
	e.buf = append(e.buf[:start], e.buf[e.cursor:]...)
	e.cursor = start
}

func (e *Editor) yankText() {
	if len(e.yank) == 0 {
		return
	}
	if e.cursor == len(e.buf) {
		e.buf = append(e.buf, e.yank...)
		e.cursor += len(e.yank)
		return
	}
	insert := append([]rune(nil), e.yank...)
	e.buf = append(e.buf[:e.cursor], append(insert, e.buf[e.cursor:]...)...)
	e.cursor += len(insert)
}

func visibleLen(s string) int {
	return len([]rune(s))
}

func currentUserName() string {
	u, err := user.Current()
	if err != nil {
		if name := os.Getenv("USER"); name != "" {
			return name
		}
		return "unknown"
	}
	if u.Username != "" {
		parts := strings.Split(u.Username, `\`)
		return parts[len(parts)-1]
	}
	return "unknown"
}

func currentHostName() string {
	h, err := os.Hostname()
	if err != nil || h == "" {
		return "unknown"
	}
	return h
}

func shortenPromptPath(path string) string {
	if path == "" {
		return path
	}

	path = filepath.ToSlash(path)

	prefix := ""
	switch {
	case path == "~":
		return "~"
	case strings.HasPrefix(path, "~/"):
		prefix = "~"
		path = strings.TrimPrefix(path, "~/")
	case path == "/":
		return "/"
	case strings.HasPrefix(path, "/"):
		prefix = "/"
		path = strings.TrimPrefix(path, "/")
	}

	if path == "" {
		return prefix
	}

	parts := strings.Split(path, "/")
	for i, part := range parts {
		if part == "" || part == "." || part == ".." {
			continue
		}
		if utf8.RuneCountInString(part) >= 4 {
			r, _ := utf8.DecodeRuneInString(part)
			parts[i] = string(r)
		}
	}

	shortened := strings.Join(parts, "/")

	switch prefix {
	case "~":
		return "~/" + shortened
	case "/":
		return "/" + shortened
	default:
		return shortened
	}
}

func currentDirName() string {
	wd, err := os.Getwd()
	if err != nil {
		return "?"
	}

	home, _ := os.UserHomeDir()
	display := wd

	if home != "" && wd == home {
		display = "~"
	} else if home != "" && strings.HasPrefix(wd, home+string(os.PathSeparator)) {
		display = "~" + strings.TrimPrefix(wd, home)
	}

	return shortenPromptPath(display)
}

func promptLine1Plain() (leftPlain string, rightPlain string) {
	now := time.Now()
	tm := now.Format("15:04:05")
	dt := now.Format("2006.01.02 Mon")

	userName := currentUserName()
	hostName := currentHostName()
	dirName := currentDirName()

	leftPlain = "[" + tm + "] " + userName + " @" + hostName + " in " + dirName
	rightPlain = dt
	return
}

func promptLine1Display() string {
	now := time.Now()
	tm := now.Format("15:04:05")
	dt := now.Format("2006.01.02 Mon")

	userName := currentUserName()
	hostName := currentHostName()
	dirName := currentDirName()

	left := "[" + colorRed + tm + colorOff + "] " + colorYellow + userName + colorOff +
	        "@" + colorGreen + hostName + colorOff + " in " + colorBlue + dirName + colorOff
	right := colorRed + dt + colorOff

	width, _, err := term.GetSize(int(os.Stdout.Fd()))
	if err != nil || width <= 0 {
		width = 80
	}

	leftPlain, rightPlain := promptLine1Plain()
	spaces := width - visibleLen(leftPlain) - visibleLen(rightPlain)
	if spaces < 1 {
		spaces = 1
	}

	return left + strings.Repeat(" ", spaces) + right + "\n" + inputPrompt
}

func printPrompt() {
	fmt.Print(promptLine1Display())
}

func (e *Editor) refresh(w io.Writer) {
	var b bytes.Buffer

	b.WriteString("\r")
	b.WriteString("\x1b[2K")
	b.WriteString("\x1b[1A")
	b.WriteString("\x1b[2K")
	b.WriteString("\r")

	b.WriteString(promptLine1Display())
	b.WriteString(string(e.buf))
	b.WriteString("\x1b[K")
	b.WriteString("\r")

	target := len([]rune(inputPrompt)) + e.cursor
	if target > 0 {
		b.WriteString(fmt.Sprintf("\x1b[%dC", target))
	}

	_, _ = w.Write(b.Bytes())
}

func clearScreen(w io.Writer) {
	fmt.Fprint(w, "\x1b[H\x1b[2J\x1b[3J")
}

func readKey(r io.Reader) ([]byte, error) {
	buf := make([]byte, 1)
	_, err := r.Read(buf)
	if err != nil {
		return nil, err
	}
	if buf[0] == 0x1b {
		seq := make([]byte, 2)
		n, _ := r.Read(seq)
		return append(buf, seq[:n]...), nil
	}
	return buf, nil
}

type History struct {
	items   []string
	index   int
	stashed string
}

func NewHistory() *History {
	return &History{
		items: make([]string, 0),
		index: 0,
	}
}

func (h *History) Add(line string) {
	line = strings.TrimSpace(line)
	if line == "" {
		h.index = len(h.items)
		h.stashed = ""
		return
	}

	if len(h.items) == 0 || h.items[len(h.items)-1] != line {
		h.items = append(h.items, line)
	}
	h.index = len(h.items)
	h.stashed = ""
}

func (h *History) Prev(current string) (string, bool) {
	if len(h.items) == 0 {
		return "", false
	}

	if h.index == len(h.items) {
		h.stashed = current
	}

	if h.index > 0 {
		h.index--
		return h.items[h.index], true
	}

	return h.items[0], true
}

func (h *History) Next() (string, bool) {
	if len(h.items) == 0 {
		return "", false
	}

	if h.index < len(h.items)-1 {
		h.index++
		return h.items[h.index], true
	}

	if h.index == len(h.items)-1 {
		h.index = len(h.items)
		return h.stashed, true
	}

	return h.stashed, true
}

func (h *History) ResetNavigation() {
	h.index = len(h.items)
	h.stashed = ""
}

func (h *History) Len() int {
	return len(h.items)
}

func (h *History) SliceLast(n int) []string {
	if n <= 0 || n >= len(h.items) {
		out := make([]string, len(h.items))
		copy(out, h.items)
		return out
	}
	out := make([]string, n)
	copy(out, h.items[len(h.items)-n:])
	return out
}

type Command struct {
	Args   []string
	Input  string
	Output string
	Append bool
}

type Pipeline struct {
	Commands []Command
}

func tokenize(line string) ([]string, error) {
	var toks []string
	var cur []rune
	inSingle := false
	inDouble := false
	escape := false

	flush := func() {
		if len(cur) > 0 {
			toks = append(toks, string(cur))
			cur = nil
		}
	}

	rs := []rune(line)
	for i := 0; i < len(rs); i++ {
		r := rs[i]

		switch {
		case escape:
			cur = append(cur, r)
			escape = false
		case r == '\\' && !inSingle:
			escape = true
		case r == '\'' && !inDouble:
			inSingle = !inSingle
		case r == '"' && !inSingle:
			inDouble = !inDouble
		case !inSingle && !inDouble && (r == ' ' || r == '\t'):
			flush()
		case !inSingle && !inDouble && r == '|':
			flush()
			toks = append(toks, "|")
		case !inSingle && !inDouble && r == '<':
			flush()
			toks = append(toks, "<")
		case !inSingle && !inDouble && r == '>':
			flush()
			if i+1 < len(rs) && rs[i+1] == '>' {
				toks = append(toks, ">>")
				i++
			} else {
				toks = append(toks, ">")
			}
		default:
			cur = append(cur, r)
		}
	}

	if escape {
		cur = append(cur, '\\')
	}
	if inSingle || inDouble {
		return nil, fmt.Errorf("unterminated quote")
	}
	flush()

	return toks, nil
}

func parsePipeline(line string) (*Pipeline, error) {
	toks, err := tokenize(line)
	if err != nil {
		return nil, err
	}
	if len(toks) == 0 {
		return &Pipeline{}, nil
	}

	var p Pipeline
	cur := Command{}
	expectFileFor := ""

	pushCmd := func() error {
		if expectFileFor != "" {
			return fmt.Errorf("redirect target missing")
		}
		if len(cur.Args) == 0 {
			return fmt.Errorf("empty command")
		}
		p.Commands = append(p.Commands, cur)
		cur = Command{}
		return nil
	}

	for _, t := range toks {
		if expectFileFor != "" {
			switch expectFileFor {
			case "<":
				cur.Input = t
			case ">":
				cur.Output = t
				cur.Append = false
			case ">>":
				cur.Output = t
				cur.Append = true
			}
			expectFileFor = ""
			continue
		}

		switch t {
		case "|":
			if err := pushCmd(); err != nil {
				return nil, err
			}
		case "<", ">", ">>":
			expectFileFor = t
		default:
			cur.Args = append(cur.Args, t)
		}
	}

	if err := pushCmd(); err != nil {
		return nil, err
	}
	return &p, nil
}

func hasGlobMeta(s string) bool {
	return strings.ContainsAny(s, "*?[")
}

func expandWildcardToken(tok string) ([]string, error) {
	if !hasGlobMeta(tok) {
		return []string{tok}, nil
	}
	matches, err := filepath.Glob(tok)
	if err != nil {
		return nil, err
	}
	if len(matches) == 0 {
		return []string{tok}, nil
	}
	return matches, nil
}

func expandWildcards(args []string) ([]string, error) {
	var out []string
	for _, a := range args {
		expanded, err := expandWildcardToken(a)
		if err != nil {
			return nil, err
		}
		out = append(out, expanded...)
	}
	return out, nil
}

func isTerminalWriter(w io.Writer) bool {
	f, ok := w.(*os.File)
	if !ok {
		return false
	}
	return term.IsTerminal(int(f.Fd()))
}

func displayName(name string, isDir bool, colorize bool) string {
	label := name
	if isDir && !strings.HasSuffix(label, "/") {
		label += "/"
	}
	if isDir && colorize {
		return colorDir + label + colorOff
	}
	return label
}

var builtinNames = []string{
	"cd", "pwd", "ls", "cat", "grep", "touch",
	"nc", "wc", "uniq", "cp", "mv", "rm",
	"rmdir", "mkdir", "history", "head", "tail",
	"cut", "sort", "more", "file", "echo", "targz",
	"md5", "sha256", "sha512",	
	"ifconfig", "curl", "math", "cal",
	"version", "help", "exit",
}

var builtinHelp = map[string]string{
	"cd":       "cd [DIR]                    Change current directory.",
	"pwd":      "pwd                         Print current working directory.",
	"ls":       "ls [-a] [-l] [PATH ...]     List files; directories are shown with trailing '/'.",
	"cat":      "cat [FILE ...]              Concatenate files to standard output.",
	"grep":     "grep PATTERN [FILE ...]     Print lines containing PATTERN.",
	"touch":    "touch FILE ...              Create files or update timestamps.",
	"nc":       "nc [-u] [-l] HOST PORT      Simple TCP/UDP client or listener.",
	"wc":       "wc [-l] [FILE ...]          Print line, word, and byte counts.",
	"uniq":     "uniq [FILE]                 Filter adjacent duplicate lines.",
	"cp":       "cp SRC DST                  Copy a file.",
	"mv":       "mv SRC DST                  Rename or move a file or directory.",
	"rm":       "rm FILE ...                 Remove files.",
	"rmdir":    "rmdir DIR ...               Remove empty directories.",
	"mkdir":    "mkdir [-p] DIR ...          Create directories.",
	"history":  "history [N]                 Show command history.",
	"head":     "head [-n N] [FILE]          Print first N lines.",
	"tail":     "tail [-n N] [FILE]          Print last N lines.",
	"cut":      "cut -d DELIM -f LIST [FILE] Extract delimited fields.",
	"sort":     "sort [-n] [-r] [FILE]       Sort lines.",
	"more":     "more [FILE]                 Pager for text output.",
	"file":     "file PATH ...               Show file type information.",
	"echo":     "echo [-n] [-e] [ARG ...]    Print arguments.",
	"targz":    "targz ARCHIVE.tar.gz INPUT...  Create a .tar.gz archive.",
	"md5":      "md5 [FILE ...]              Print MD5 checksums.",
	"sha256":   "sha256 [FILE ...]           Print SHA-256 checksums.",
	"sha512":   "sha512 [FILE ...]           Print SHA-512 checksums.",
	"ifconfig": "ifconfig                    Show local IPv4, DNS, gateway, mask, MAC.",
	"curl":     "curl [OPTIONS] URL          Minimal HTTP/HTTPS client.",
	"math":     "math [-s N] [-b BASE] EXPR  Evaluate arithmetic expressions like fish math.",
	"cal":      "cal [YEAR [MONTH]] Display calendar. Today is highlighted in green.",
	"version":  "version Print shell version.",
	"help":     "help [COMMAND ...]          Show built-in command help.",
	"exit":     "exit                        Exit the shell.",
}

func isWordByte(b rune) bool {
	switch b {
	case ' ', '\t', '|', '<', '>':
		return false
	default:
		return true
	}
}

func currentTokenRange(buf []rune, cursor int) (start, end int) {
	if cursor < 0 {
		cursor = 0
	}
	if cursor > len(buf) {
		cursor = len(buf)
	}

	start = cursor
	for start > 0 && isWordByte(buf[start-1]) {
		start--
	}

	end = cursor
	for end < len(buf) && isWordByte(buf[end]) {
		end++
	}

	return
}

func tokenIndexAtCursor(buf []rune, cursor int) int {
	idx := 0
	inToken := false

	for i := 0; i < cursor && i < len(buf); i++ {
		r := buf[i]
		if isWordByte(r) {
			if !inToken {
				inToken = true
			}
		} else {
			if inToken {
				idx++
				inToken = false
			}
		}
	}
	if inToken {
		return idx
	}
	return idx
}

func uniqueSorted(xs []string) []string {
	m := map[string]struct{}{}
	for _, x := range xs {
		m[x] = struct{}{}
	}
	out := make([]string, 0, len(m))
	for x := range m {
		out = append(out, x)
	}
	sort.Strings(out)
	return out
}

func longestCommonPrefix(xs []string) string {
	if len(xs) == 0 {
		return ""
	}
	p := xs[0]
	for _, s := range xs[1:] {
		for !strings.HasPrefix(s, p) {
			if p == "" {
				return ""
			}
			p = p[:len(p)-1]
		}
	}
	return p
}

func executableCommandsFromPATH() []string {
	pathEnv := os.Getenv("PATH")
	if pathEnv == "" {
		return nil
	}

	var out []string
	for _, dir := range filepath.SplitList(pathEnv) {
		entries, err := os.ReadDir(dir)
		if err != nil {
			continue
		}
		for _, ent := range entries {
			if ent.IsDir() {
				continue
			}
			info, err := ent.Info()
			if err != nil {
				continue
			}
			if info.Mode()&0111 != 0 {
				out = append(out, ent.Name())
			}
		}
	}
	return uniqueSorted(out)
}

func commandCandidates(prefix string) []string {
	var all []string
	all = append(all, builtinNames...)
	all = append(all, executableCommandsFromPATH()...)
	all = uniqueSorted(all)

	var hits []string
	for _, s := range all {
		if strings.HasPrefix(s, prefix) {
			hits = append(hits, s)
		}
	}
	return hits
}

func splitPathForCompletion(prefix string) (dirPart, basePart string) {
	if prefix == "" {
		return ".", ""
	}

	if strings.Contains(prefix, "/") {
		dirPart = filepath.Dir(prefix)
		basePart = filepath.Base(prefix)
		if dirPart == "" {
			dirPart = "."
		}
		return
	}

	return ".", prefix
}

func pathCandidates(prefix string) []string {
	dirPart, basePart := splitPathForCompletion(prefix)

	entries, err := os.ReadDir(dirPart)
	if err != nil {
		return nil
	}

	var hits []string
	for _, ent := range entries {
		name := ent.Name()
		if strings.HasPrefix(name, basePart) {
			full := name
			if dirPart != "." {
				full = filepath.Join(dirPart, name)
			}
			if ent.IsDir() {
				full += "/"
			}
			hits = append(hits, full)
		}
	}

	sort.Strings(hits)
	return hits
}

func completeAtCursor(e *Editor) {
	start, end := currentTokenRange(e.buf, e.cursor)
	token := string(e.buf[start:e.cursor])
	index := tokenIndexAtCursor(e.buf, start)

	var candidates []string
	if index == 0 {
		candidates = commandCandidates(token)
	} else {
		candidates = pathCandidates(token)
	}

	if len(candidates) == 0 {
		return
	}

	if len(candidates) == 1 {
		e.replaceRange(start, end, candidates[0])
		return
	}

	lcp := longestCommonPrefix(candidates)
	if lcp != "" && lcp != token {
		e.replaceRange(start, end, lcp)
		return
	}

	fmt.Print("\r\n")
	for _, c := range candidates {
		fmt.Println(c)
	}
	e.refresh(os.Stdout)
}

func builtinCD(args []string, stdout, stderr io.Writer) int {
	dir := ""
	if len(args) < 2 {
		home, err := os.UserHomeDir()
		if err != nil {
			fmt.Fprintf(stderr, "cd: %v\n", err)
			return 1
		}
		dir = home
	} else {
		dir = args[1]
	}

	if err := os.Chdir(dir); err != nil {
		fmt.Fprintf(stderr, "cd: %v\n", err)
		return 1
	}
	return 0
}

func builtinPWD(stdout, stderr io.Writer) int {
	wd, err := os.Getwd()
	if err != nil {
		fmt.Fprintf(stderr, "pwd: %v\n", err)
		return 1
	}
	fmt.Fprintln(stdout, wd)
	return 0
}

func printLong(w io.Writer, name string, info os.FileInfo, colorize bool) {
	mode := info.Mode().String()
	size := info.Size()
	mod := info.ModTime().Format("2006-01-02 15:04")
	display := displayName(name, info.IsDir(), colorize)
	fmt.Fprintf(w, "%s %10d %s %s\n", mode, size, mod, display)
}

func builtinLS(args []string, stdout, stderr io.Writer) int {
	showAll := false
	longFmt := false
	var rawPaths []string

	for _, a := range args[1:] {
		if strings.HasPrefix(a, "-") && len(a) > 1 {
			for _, ch := range a[1:] {
				switch ch {
				case 'a':
					showAll = true
				case 'l':
					longFmt = true
				default:
					fmt.Fprintf(stderr, "ls: unsupported option -%c\n", ch)
					return 1
				}
			}
		} else {
			rawPaths = append(rawPaths, a)
		}
	}

	var paths []string
	if len(rawPaths) == 0 {
		paths = []string{"."}
	} else {
		expanded, err := expandWildcards(rawPaths)
		if err != nil {
			fmt.Fprintf(stderr, "ls: glob error: %v\n", err)
			return 1
		}
		paths = expanded
	}

	multi := len(paths) > 1
	colorize := isTerminalWriter(stdout)
	status := 0

	for i, path := range paths {
		info, err := os.Stat(path)
		if err != nil {
			fmt.Fprintf(stderr, "ls: %s: %v\n", path, err)
			status = 1
			continue
		}

		if multi {
			if i > 0 {
				fmt.Fprintln(stdout)
			}
			title := displayName(path, info.IsDir(), colorize)
			fmt.Fprintf(stdout, "%s:\n", title)
		}

		if !info.IsDir() {
			if longFmt {
				printLong(stdout, path, info, colorize)
			} else {
				fmt.Fprintln(stdout, displayName(filepath.Base(path), info.IsDir(), colorize))
			}
			continue
		}

		entries, err := os.ReadDir(path)
		if err != nil {
			fmt.Fprintf(stderr, "ls: %s: %v\n", path, err)
			status = 1
			continue
		}

		for _, entry := range entries {
			name := entry.Name()
			if !showAll && strings.HasPrefix(name, ".") {
				continue
			}

			if longFmt {
				full := filepath.Join(path, name)
				fi, err := os.Stat(full)
				if err != nil {
					fmt.Fprintf(stderr, "ls: %s: %v\n", full, err)
					status = 1
					continue
				}
				printLong(stdout, name, fi, colorize)
			} else {
				fmt.Fprintln(stdout, displayName(name, entry.IsDir(), colorize))
			}
		}
	}

	return status
}

func catReader(out io.Writer, name string, r io.Reader) error {
	_, err := io.Copy(out, r)
	if err != nil {
		return fmt.Errorf("cat: %s: %w", name, err)
	}
	return nil
}

func builtinCAT(args []string, stdin io.Reader, stdout, stderr io.Writer) int {
	if len(args) == 1 {
		if err := catReader(stdout, "<stdin>", stdin); err != nil {
			fmt.Fprintln(stderr, err)
			return 1
		}
		return 0
	}

	files, err := expandWildcards(args[1:])
	if err != nil {
		fmt.Fprintf(stderr, "cat: glob error: %v\n", err)
		return 1
	}

	status := 0
	for _, file := range files {
		f, err := os.Open(file)
		if err != nil {
			fmt.Fprintf(stderr, "cat: %s: %v\n", file, err)
			status = 1
			continue
		}
		err = catReader(stdout, file, f)
		_ = f.Close()
		if err != nil {
			fmt.Fprintln(stderr, err)
			status = 1
		}
	}
	return status
}

func grepReader(pattern string, r io.Reader, out io.Writer, label string, showName bool) error {
	scanner := bufio.NewScanner(r)
	buf := make([]byte, 0, 64*1024)
	scanner.Buffer(buf, 1024*1024)

	for scanner.Scan() {
		line := scanner.Text()
		if strings.Contains(line, pattern) {
			if showName {
				fmt.Fprintf(out, "%s:%s\n", label, line)
			} else {
				fmt.Fprintln(out, line)
			}
		}
	}
	if err := scanner.Err(); err != nil {
		return fmt.Errorf("grep: %s: %w", label, err)
	}
	return nil
}

func builtinGREP(args []string, stdin io.Reader, stdout, stderr io.Writer) int {
	if len(args) < 2 {
		fmt.Fprintln(stderr, "usage: grep PATTERN [FILE ...]")
		return 1
	}

	pattern := args[1]

	if len(args) == 2 {
		if err := grepReader(pattern, stdin, stdout, "<stdin>", false); err != nil {
			fmt.Fprintln(stderr, err)
			return 1
		}
		return 0
	}

	files, err := expandWildcards(args[2:])
	if err != nil {
		fmt.Fprintf(stderr, "grep: glob error: %v\n", err)
		return 1
	}

	showName := len(files) > 1
	status := 0

	for _, file := range files {
		f, err := os.Open(file)
		if err != nil {
			fmt.Fprintf(stderr, "grep: %s: %v\n", file, err)
			status = 1
			continue
		}
		err = grepReader(pattern, f, stdout, file, showName)
		_ = f.Close()
		if err != nil {
			fmt.Fprintln(stderr, err)
			status = 1
		}
	}

	return status
}

func touchOne(path string) error {
	now := time.Now()

	f, err := os.OpenFile(path, os.O_RDONLY|os.O_CREATE, 0644)
	if err != nil {
		return err
	}
	_ = f.Close()

	return os.Chtimes(path, now, now)
}

func builtinTOUCH(args []string, stdout, stderr io.Writer) int {
	if len(args) < 2 {
		fmt.Fprintln(stderr, "usage: touch FILE ...")
		return 1
	}

	paths, err := expandWildcards(args[1:])
	if err != nil {
		fmt.Fprintf(stderr, "touch: glob error: %v\n", err)
		return 1
	}

	status := 0
	for _, path := range paths {
		if err := touchOne(path); err != nil {
			fmt.Fprintf(stderr, "touch: %s: %v\n", path, err)
			status = 1
		}
	}
	return status
}

type ncConfig struct {
	udp    bool
	listen bool
	host   string
	port   string
}

func parseNCArgs(args []string) (*ncConfig, error) {
	cfg := &ncConfig{}
	var pos []string

	for i := 1; i < len(args); i++ {
		a := args[i]
		switch a {
		case "-u":
			cfg.udp = true
		case "-l":
			cfg.listen = true
		default:
			pos = append(pos, a)
		}
	}

	if cfg.listen {
		if len(pos) != 1 {
			return nil, fmt.Errorf("usage: nc [-u] -l PORT")
		}
		cfg.port = pos[0]
		return cfg, nil
	}

	if len(pos) != 2 {
		return nil, fmt.Errorf("usage: nc [-u] HOST PORT")
	}
	cfg.host = pos[0]
	cfg.port = pos[1]
	return cfg, nil
}

func copyAndClose(dst io.WriteCloser, src io.Reader, wg *sync.WaitGroup) {
	defer wg.Done()
	_, _ = io.Copy(dst, src)
	_ = dst.Close()
}

func runNCTCPClient(cfg *ncConfig, stdin io.Reader, stdout, stderr io.Writer) int {
	conn, err := net.Dial("tcp", net.JoinHostPort(cfg.host, cfg.port))
	if err != nil {
		fmt.Fprintf(stderr, "nc: %v\n", err)
		return 1
	}
	defer conn.Close()

	var wg sync.WaitGroup
	wg.Add(2)

	go copyAndClose(conn, stdin, &wg)
	go func() {
		defer wg.Done()
		_, _ = io.Copy(stdout, conn)
	}()

	wg.Wait()
	return 0
}

func runNCTCPListen(cfg *ncConfig, stdin io.Reader, stdout, stderr io.Writer) int {
	ln, err := net.Listen("tcp", ":"+cfg.port)
	if err != nil {
		fmt.Fprintf(stderr, "nc: %v\n", err)
		return 1
	}
	defer ln.Close()

	conn, err := ln.Accept()
	if err != nil {
		fmt.Fprintf(stderr, "nc: %v\n", err)
		return 1
	}
	defer conn.Close()

	var wg sync.WaitGroup
	wg.Add(2)

	go copyAndClose(conn, stdin, &wg)
	go func() {
		defer wg.Done()
		_, _ = io.Copy(stdout, conn)
	}()

	wg.Wait()
	return 0
}

func runNCUDPClient(cfg *ncConfig, stdin io.Reader, stdout, stderr io.Writer) int {
	conn, err := net.Dial("udp", net.JoinHostPort(cfg.host, cfg.port))
	if err != nil {
		fmt.Fprintf(stderr, "nc: %v\n", err)
		return 1
	}
	defer conn.Close()

	var wg sync.WaitGroup
	wg.Add(2)

	go func() {
		defer wg.Done()
		buf := make([]byte, 65535)
		for {
			n, err := conn.Read(buf)
			if n > 0 {
				_, _ = stdout.Write(buf[:n])
			}
			if err != nil {
				return
			}
		}
	}()

	go func() {
		defer wg.Done()
		buf := make([]byte, 65535)
		for {
			n, err := stdin.Read(buf)
			if n > 0 {
				_, _ = conn.Write(buf[:n])
			}
			if err != nil {
				return
			}
		}
	}()

	wg.Wait()
	return 0
}

func runNCUDPListen(cfg *ncConfig, stdin io.Reader, stdout, stderr io.Writer) int {
	pc, err := net.ListenPacket("udp", ":"+cfg.port)
	if err != nil {
		fmt.Fprintf(stderr, "nc: %v\n", err)
		return 1
	}
	defer pc.Close()

	udpConn, ok := pc.(*net.UDPConn)
	if !ok {
		fmt.Fprintln(stderr, "nc: failed to create UDP listener")
		return 1
	}

	buf := make([]byte, 65535)

	n, addr, err := udpConn.ReadFrom(buf)
	if err != nil {
		fmt.Fprintf(stderr, "nc: %v\n", err)
		return 1
	}
	if n > 0 {
		_, _ = stdout.Write(buf[:n])
	}

	var wg sync.WaitGroup
	wg.Add(2)

	go func() {
		defer wg.Done()
		for {
			n, _, err := udpConn.ReadFrom(buf)
			if n > 0 {
				_, _ = stdout.Write(buf[:n])
			}
			if err != nil {
				return
			}
		}
	}()

	go func(remote net.Addr) {
		defer wg.Done()
		inbuf := make([]byte, 65535)
		for {
			n, err := stdin.Read(inbuf)
			if n > 0 {
				_, _ = udpConn.WriteTo(inbuf[:n], remote)
			}
			if err != nil {
				return
			}
		}
	}(addr)

	wg.Wait()
	return 0
}

func builtinNC(args []string, stdin io.Reader, stdout, stderr io.Writer) int {
	cfg, err := parseNCArgs(args)
	if err != nil {
		fmt.Fprintf(stderr, "nc: %v\n", err)
		return 1
	}

	switch {
	case cfg.udp && cfg.listen:
		return runNCUDPListen(cfg, stdin, stdout, stderr)
	case cfg.udp && !cfg.listen:
		return runNCUDPClient(cfg, stdin, stdout, stderr)
	case !cfg.udp && cfg.listen:
		return runNCTCPListen(cfg, stdin, stdout, stderr)
	default:
		return runNCTCPClient(cfg, stdin, stdout, stderr)
	}
}

type wcResult struct {
	lines int
	words int
	bytes int
}

func countWC(r io.Reader) (wcResult, error) {
	var res wcResult
	br := bufio.NewReader(r)
	inWord := false

	for {
		b, err := br.ReadByte()
		if err == io.EOF {
			break
		}
		if err != nil {
			return res, err
		}

		res.bytes++
		if b == '\n' {
			res.lines++
		}

		if unicode.IsSpace(rune(b)) {
			inWord = false
		} else if !inWord {
			res.words++
			inWord = true
		}
	}

	return res, nil
}

func printWC(w io.Writer, res wcResult, label string, linesOnly bool) {
	if linesOnly {
		if label == "" {
			fmt.Fprintf(w, "%8d\n", res.lines)
		} else {
			fmt.Fprintf(w, "%8d %s\n", res.lines, label)
		}
		return
	}
	if label == "" {
		fmt.Fprintf(w, "%8d %8d %8d\n", res.lines, res.words, res.bytes)
	} else {
		fmt.Fprintf(w, "%8d %8d %8d %s\n", res.lines, res.words, res.bytes, label)
	}
}

func builtinWC(args []string, stdin io.Reader, stdout, stderr io.Writer) int {
	linesOnly := false
	for _, a := range args[1:] {
		if a == "-l" {
			linesOnly = true
			continue
		}
	}
	if len(args) == 1 {
		res, err := countWC(stdin)
		if err != nil {
			fmt.Fprintf(stderr, "wc: %v\n", err)
			return 1
		}
		printWC(stdout, res, "", linesOnly)
		return 0
	}

	files, err := expandWildcards(args[1:])
	if err != nil {
		fmt.Fprintf(stderr, "wc: glob error: %v\n", err)
		return 1
	}

	total := wcResult{}
	status := 0

	for _, file := range files {
		f, err := os.Open(file)
		if err != nil {
			fmt.Fprintf(stderr, "wc: %s: %v\n", file, err)
			status = 1
			continue
		}
		res, err := countWC(f)
		_ = f.Close()
		if err != nil {
			fmt.Fprintf(stderr, "wc: %s: %v\n", file, err)
			status = 1
			continue
		}
		printWC(stdout, res, file, linesOnly)
		total.lines += res.lines
		total.words += res.words
		total.bytes += res.bytes
	}

	if len(files) > 1 {
		printWC(stdout, total, "total", linesOnly)
	}
	return status
}

func builtinUNIQ(args []string, stdin io.Reader, stdout, stderr io.Writer) int {
	if len(args) > 2 {
		fmt.Fprintln(stderr, "usage: uniq [FILE]")
		return 1
	}

	var r io.Reader = stdin
	var file string
	if len(args) == 2 {
		file = args[1]
		files, err := expandWildcards([]string{file})
		if err != nil {
			fmt.Fprintf(stderr, "uniq: glob error: %v\n", err)
			return 1
		}
		if len(files) != 1 {
			fmt.Fprintln(stderr, "uniq: expected exactly one input file")
			return 1
		}
		f, err := os.Open(files[0])
		if err != nil {
			fmt.Fprintf(stderr, "uniq: %s: %v\n", files[0], err)
			return 1
		}
		defer f.Close()
		r = f
	}

	scanner := bufio.NewScanner(r)
	buf := make([]byte, 0, 64*1024)
	scanner.Buffer(buf, 1024*1024)

	first := true
	prev := ""
	for scanner.Scan() {
		line := scanner.Text()
		if first || line != prev {
			fmt.Fprintln(stdout, line)
			prev = line
			first = false
		}
	}
	if err := scanner.Err(); err != nil {
		if file == "" {
			fmt.Fprintf(stderr, "uniq: %v\n", err)
		} else {
			fmt.Fprintf(stderr, "uniq: %s: %v\n", file, err)
		}
		return 1
	}
	return 0
}

func copyFile(src, dst string) error {
	in, err := os.Open(src)
	if err != nil {
		return err
	}
	defer in.Close()

	info, err := in.Stat()
	if err != nil {
		return err
	}
	if info.IsDir() {
		return fmt.Errorf("is a directory")
	}

	out, err := os.OpenFile(dst, os.O_CREATE|os.O_WRONLY|os.O_TRUNC, info.Mode().Perm())
	if err != nil {
		return err
	}
	defer out.Close()

	if _, err := io.Copy(out, in); err != nil {
		return err
	}
	return out.Sync()
}

func builtinCP(args []string, stdout, stderr io.Writer) int {
	if len(args) != 3 {
		fmt.Fprintln(stderr, "usage: cp SRC DST")
		return 1
	}

	srcs, err := expandWildcards([]string{args[1]})
	if err != nil {
		fmt.Fprintf(stderr, "cp: glob error: %v\n", err)
		return 1
	}
	if len(srcs) != 1 {
		fmt.Fprintln(stderr, "cp: source must resolve to exactly one file")
		return 1
	}

	src := srcs[0]
	dst := args[2]

	if err := copyFile(src, dst); err != nil {
		fmt.Fprintf(stderr, "cp: %v\n", err)
		return 1
	}
	return 0
}

func builtinMV(args []string, stdout, stderr io.Writer) int {
	if len(args) != 3 {
		fmt.Fprintln(stderr, "usage: mv SRC DST")
		return 1
	}

	srcs, err := expandWildcards([]string{args[1]})
	if err != nil {
		fmt.Fprintf(stderr, "mv: glob error: %v\n", err)
		return 1
	}
	if len(srcs) != 1 {
		fmt.Fprintln(stderr, "mv: source must resolve to exactly one path")
		return 1
	}

	if err := os.Rename(srcs[0], args[2]); err != nil {
		fmt.Fprintf(stderr, "mv: %v\n", err)
		return 1
	}
	return 0
}

func builtinRM(args []string, stdout, stderr io.Writer) int {
	if len(args) < 2 {
		fmt.Fprintln(stderr, "usage: rm FILE ...")
		return 1
	}

	files, err := expandWildcards(args[1:])
	if err != nil {
		fmt.Fprintf(stderr, "rm: glob error: %v\n", err)
		return 1
	}

	status := 0
	for _, file := range files {
		info, err := os.Stat(file)
		if err != nil {
			fmt.Fprintf(stderr, "rm: %s: %v\n", file, err)
			status = 1
			continue
		}
		if info.IsDir() {
			fmt.Fprintf(stderr, "rm: %s: is a directory\n", file)
			status = 1
			continue
		}
		if err := os.Remove(file); err != nil {
			fmt.Fprintf(stderr, "rm: %s: %v\n", file, err)
			status = 1
		}
	}
	return status
}

func builtinRMDIR(args []string, stdout, stderr io.Writer) int {
	if len(args) < 2 {
		fmt.Fprintln(stderr, "usage: rmdir DIR ...")
		return 1
	}

	dirs, err := expandWildcards(args[1:])
	if err != nil {
		fmt.Fprintf(stderr, "rmdir: glob error: %v\n", err)
		return 1
	}

	status := 0
	for _, dir := range dirs {
		if err := os.Remove(dir); err != nil {
			fmt.Fprintf(stderr, "rmdir: %s: %v\n", dir, err)
			status = 1
		}
	}
	return status
}

func builtinMKDIR(args []string, stdout, stderr io.Writer) int {
	if len(args) < 2 {
		fmt.Fprintln(stderr, "usage: mkdir [-p] DIR ...")
		return 1
	}

	withParents := false
	var dirs []string

	for _, a := range args[1:] {
		if a == "-p" {
			withParents = true
		} else {
			dirs = append(dirs, a)
		}
	}

	if len(dirs) == 0 {
		fmt.Fprintln(stderr, "mkdir: missing operand")
		return 1
	}

	status := 0
	for _, d := range dirs {
		if withParents {
			if err := os.MkdirAll(d, 0755); err != nil {
				fmt.Fprintf(stderr, "mkdir: %s: %v\n", d, err)
				status = 1
			}
		} else {
			if err := os.Mkdir(d, 0755); err != nil {
				fmt.Fprintf(stderr, "mkdir: %s: %v\n", d, err)
				status = 1
			}
		}
	}
	return status
}

func builtinHISTORY(args []string, hist *History, stdout, stderr io.Writer) int {
	if len(args) > 2 {
		fmt.Fprintln(stderr, "usage: history [N]")
		return 1
	}

	if len(args) == 1 {
		for i, cmd := range hist.items {
			fmt.Fprintf(stdout, "%5d  %s\n", i+1, cmd)
		}
		return 0
	}

	var n int
	_, err := fmt.Sscanf(args[1], "%d", &n)
	if err != nil || n < 0 {
		fmt.Fprintln(stderr, "history: N must be a non-negative integer")
		return 1
	}

	items := hist.SliceLast(n)
	start := hist.Len() - len(items) + 1
	for i, cmd := range items {
		fmt.Fprintf(stdout, "%5d  %s\n", start+i, cmd)
	}
	return 0
}

func parseLineCountArgs(cmdName string, args []string) (n int, file string, err error) {
	n = 10

	if len(args) == 1 {
		return n, "", nil
	}

	i := 1
	if i < len(args) && args[i] == "-n" {
		if i+1 >= len(args) {
			return 0, "", fmt.Errorf("%s: option requires an argument -- n", cmdName)
		}
		_, scanErr := fmt.Sscanf(args[i+1], "%d", &n)
		if scanErr != nil || n < 0 {
			return 0, "", fmt.Errorf("%s: invalid number of lines: %s", cmdName, args[i+1])
		}
		i += 2
	}

	if i < len(args) {
		file = args[i]
		i++
	}
	if i != len(args) {
		return 0, "", fmt.Errorf("usage: %s [-n N] [FILE]", cmdName)
	}

	return n, file, nil
}

func headReader(r io.Reader, n int, out io.Writer) error {
	scanner := bufio.NewScanner(r)
	buf := make([]byte, 0, 64*1024)
	scanner.Buffer(buf, 1024*1024)

	count := 0
	for scanner.Scan() {
		if count >= n {
			break
		}
		fmt.Fprintln(out, scanner.Text())
		count++
	}
	return scanner.Err()
}

func builtinHEAD(args []string, stdin io.Reader, stdout, stderr io.Writer) int {
	n, file, err := parseLineCountArgs("head", args)
	if err != nil {
		fmt.Fprintln(stderr, err)
		return 1
	}

	var r io.Reader = stdin
	if file != "" {
		files, err := expandWildcards([]string{file})
		if err != nil {
			fmt.Fprintf(stderr, "head: glob error: %v\n", err)
			return 1
		}
		if len(files) != 1 {
			fmt.Fprintln(stderr, "head: expected exactly one input file")
			return 1
		}
		f, err := os.Open(files[0])
		if err != nil {
			fmt.Fprintf(stderr, "head: %s: %v\n", files[0], err)
			return 1
		}
		defer f.Close()
		r = f
	}

	if err := headReader(r, n, stdout); err != nil {
		if file == "" {
			fmt.Fprintf(stderr, "head: %v\n", err)
		} else {
			fmt.Fprintf(stderr, "head: %s: %v\n", file, err)
		}
		return 1
	}
	return 0
}

func tailReader(r io.Reader, n int, out io.Writer) error {
	if n == 0 {
		return nil
	}

	scanner := bufio.NewScanner(r)
	buf := make([]byte, 0, 64*1024)
	scanner.Buffer(buf, 1024*1024)

	lines := make([]string, 0, n)

	for scanner.Scan() {
		line := scanner.Text()
		if len(lines) < n {
			lines = append(lines, line)
		} else {
			copy(lines, lines[1:])
			lines[n-1] = line
		}
	}
	if err := scanner.Err(); err != nil {
		return err
	}

	for _, line := range lines {
		fmt.Fprintln(out, line)
	}
	return nil
}

func builtinTAIL(args []string, stdin io.Reader, stdout, stderr io.Writer) int {
	n, file, err := parseLineCountArgs("tail", args)
	if err != nil {
		fmt.Fprintln(stderr, err)
		return 1
	}

	var r io.Reader = stdin
	if file != "" {
		files, err := expandWildcards([]string{file})
		if err != nil {
			fmt.Fprintf(stderr, "tail: glob error: %v\n", err)
			return 1
		}
		if len(files) != 1 {
			fmt.Fprintln(stderr, "tail: expected exactly one input file")
			return 1
		}
		f, err := os.Open(files[0])
		if err != nil {
			fmt.Fprintf(stderr, "tail: %s: %v\n", files[0], err)
			return 1
		}
		defer f.Close()
		r = f
	}

	if err := tailReader(r, n, stdout); err != nil {
		if file == "" {
			fmt.Fprintf(stderr, "tail: %v\n", err)
		} else {
			fmt.Fprintf(stderr, "tail: %s: %v\n", file, err)
		}
		return 1
	}
	return 0
}

func parseCutFieldList(spec string) ([]int, error) {
	parts := strings.Split(spec, ",")
	fields := make([]int, 0, len(parts))

	for _, p := range parts {
		var n int
		_, err := fmt.Sscanf(strings.TrimSpace(p), "%d", &n)
		if err != nil || n <= 0 {
			return nil, fmt.Errorf("invalid field list: %s", spec)
		}
		fields = append(fields, n)
	}
	return fields, nil
}

func cutLineByDelimiter(line string, delim string, fields []int) string {
	cols := strings.Split(line, delim)
	out := make([]string, 0, len(fields))

	for _, f := range fields {
		idx := f - 1
		if idx >= 0 && idx < len(cols) {
			out = append(out, cols[idx])
		}
	}
	return strings.Join(out, delim)
}

func builtinCUT(args []string, stdin io.Reader, stdout, stderr io.Writer) int {
	if len(args) < 5 {
		fmt.Fprintln(stderr, "usage: cut -d DELIM -f LIST [FILE]")
		return 1
	}

	var delim string
	var fieldSpec string
	var file string

	i := 1
	for i < len(args) {
		switch args[i] {
		case "-d":
			if i+1 >= len(args) {
				fmt.Fprintln(stderr, "cut: option requires an argument -- d")
				return 1
			}
			delim = args[i+1]
			i += 2
		case "-f":
			if i+1 >= len(args) {
				fmt.Fprintln(stderr, "cut: option requires an argument -- f")
				return 1
			}
			fieldSpec = args[i+1]
			i += 2
		default:
			file = args[i]
			i++
		}
	}

	if delim == "" || fieldSpec == "" {
		fmt.Fprintln(stderr, "usage: cut -d DELIM -f LIST [FILE]")
		return 1
	}

	fields, err := parseCutFieldList(fieldSpec)
	if err != nil {
		fmt.Fprintf(stderr, "cut: %v\n", err)
		return 1
	}

	var r io.Reader = stdin
	if file != "" {
		files, err := expandWildcards([]string{file})
		if err != nil {
			fmt.Fprintf(stderr, "cut: glob error: %v\n", err)
			return 1
		}
		if len(files) != 1 {
			fmt.Fprintln(stderr, "cut: expected exactly one input file")
			return 1
		}
		f, err := os.Open(files[0])
		if err != nil {
			fmt.Fprintf(stderr, "cut: %s: %v\n", files[0], err)
			return 1
		}
		defer f.Close()
		r = f
	}

	scanner := bufio.NewScanner(r)
	buf := make([]byte, 0, 64*1024)
	scanner.Buffer(buf, 1024*1024)

	for scanner.Scan() {
		line := scanner.Text()
		fmt.Fprintln(stdout, cutLineByDelimiter(line, delim, fields))
	}
	if err := scanner.Err(); err != nil {
		if file == "" {
			fmt.Fprintf(stderr, "cut: %v\n", err)
		} else {
			fmt.Fprintf(stderr, "cut: %s: %v\n", file, err)
		}
		return 1
	}

	return 0
}

func readAllLines(r io.Reader) ([]string, error) {
	scanner := bufio.NewScanner(r)
	buf := make([]byte, 0, 64*1024)
	scanner.Buffer(buf, 1024*1024)

	var lines []string
	for scanner.Scan() {
		lines = append(lines, scanner.Text())
	}
	return lines, scanner.Err()
}

func builtinSORT(args []string, stdin io.Reader, stdout, stderr io.Writer) int {
	reverse := false
	numeric := false
	var file string

	for i := 1; i < len(args); i++ {
		switch args[i] {
		case "-r":
			reverse = true
		case "-n":
			numeric = true
		default:
			file = args[i]
		}
	}

	var r io.Reader = stdin
	if file != "" {
		files, err := expandWildcards([]string{file})
		if err != nil {
			fmt.Fprintf(stderr, "sort: glob error: %v\n", err)
			return 1
		}
		if len(files) != 1 {
			fmt.Fprintln(stderr, "sort: expected exactly one input file")
			return 1
		}
		f, err := os.Open(files[0])
		if err != nil {
			fmt.Fprintf(stderr, "sort: %s: %v\n", files[0], err)
			return 1
		}
		defer f.Close()
		r = f
	}

	lines, err := readAllLines(r)
	if err != nil {
		if file == "" {
			fmt.Fprintf(stderr, "sort: %v\n", err)
		} else {
			fmt.Fprintf(stderr, "sort: %s: %v\n", file, err)
		}
		return 1
	}

	if numeric {
		sort.Slice(lines, func(i, j int) bool {
			var ai, aj float64
			_, err1 := fmt.Sscanf(strings.TrimSpace(lines[i]), "%f", &ai)
			_, err2 := fmt.Sscanf(strings.TrimSpace(lines[j]), "%f", &aj)

			if err1 != nil || err2 != nil {
				if reverse {
					return lines[i] > lines[j]
				}
				return lines[i] < lines[j]
			}

			if reverse {
				return ai > aj
			}
			return ai < aj
		})
	} else {
		sort.Strings(lines)
		if reverse {
			for i, j := 0, len(lines)-1; i < j; i, j = i+1, j-1 {
				lines[i], lines[j] = lines[j], lines[i]
			}
		}
	}

	for _, line := range lines {
		fmt.Fprintln(stdout, line)
	}
	return 0
}

func terminalHeight() int {
	_, h, err := term.GetSize(int(os.Stdout.Fd()))
	if err != nil || h <= 0 {
		return 24
	}
	return h
}

func clearCurrentLine(w io.Writer) {
	fmt.Fprint(w, "\r\x1b[2K")
}

func readOneByte(r io.Reader) (byte, error) {
	var b [1]byte
	_, err := r.Read(b[:])
	return b[0], err
}

func moreReader(r io.Reader, stdin io.Reader, stdout, stderr io.Writer) int {
	scanner := bufio.NewScanner(r)
	buf := make([]byte, 0, 64*1024)
	scanner.Buffer(buf, 1024*1024)

	pageLines := terminalHeight() - 1
	if pageLines < 1 {
		pageLines = 1
	}

	shown := 0

	for scanner.Scan() {
		fmt.Fprintln(stdout, scanner.Text())
		shown++

		if shown >= pageLines {
			fmt.Fprint(stdout, "--More--")
			key, err := readOneByte(stdin)
			clearCurrentLine(stdout)
			if err != nil {
				fmt.Fprintf(stderr, "more: %v\n", err)
				return 1
			}

			switch key {
			case 'q', 'Q':
				return 0
			case ' ':
				shown = 0
			case '\r', '\n':
				shown = pageLines - 1
			default:
				shown = 0
			}
		}
	}

	if err := scanner.Err(); err != nil {
		fmt.Fprintf(stderr, "more: %v\n", err)
		return 1
	}
	return 0
}

func builtinMORE(args []string, stdin io.Reader, stdout, stderr io.Writer) int {
	if len(args) > 2 {
		fmt.Fprintln(stderr, "usage: more [FILE]")
		return 1
	}

	var r io.Reader = stdin
	var file string

	if len(args) == 2 {
		file = args[1]
		files, err := expandWildcards([]string{file})
		if err != nil {
			fmt.Fprintf(stderr, "more: glob error: %v\n", err)
			return 1
		}
		if len(files) != 1 {
			fmt.Fprintln(stderr, "more: expected exactly one input file")
			return 1
		}
		f, err := os.Open(files[0])
		if err != nil {
			fmt.Fprintf(stderr, "more: %s: %v\n", files[0], err)
			return 1
		}
		defer f.Close()
		r = f
	}

	return moreReader(r, os.Stdin, stdout, stderr)
}

func isLikelyText(data []byte) bool {
	if len(data) == 0 {
		return true
	}
	if bytes.HasPrefix(data, []byte{0xEF, 0xBB, 0xBF}) {
		return true
	}
	if !utf8.Valid(data) {
		return false
	}
	bad := 0
	for _, r := range string(data) {
		if r == '\n' || r == '\r' || r == '\t' {
			continue
		}
		if r < 32 && !unicode.IsSpace(r) {
			bad++
		}
	}
	return bad == 0
}

func describeFile(path string) (string, error) {
	info, err := os.Lstat(path)
	if err != nil {
		return "", err
	}

	mode := info.Mode()

	switch {
	case mode&os.ModeSymlink != 0:
		target, err := os.Readlink(path)
		if err != nil {
			return "symbolic link", nil
		}
		return "symbolic link to " + target, nil
	case mode.IsDir():
		return "directory", nil
	case mode&os.ModeNamedPipe != 0:
		return "named pipe", nil
	case mode&os.ModeSocket != 0:
		return "socket", nil
	case mode&os.ModeDevice != 0:
		if mode&os.ModeCharDevice != 0 {
			return "character device", nil
		}
		return "block device", nil
	}

	f, err := os.Open(path)
	if err != nil {
		return "", err
	}
	defer f.Close()

	buf := make([]byte, 512)
	n, err := f.Read(buf)
	if err != nil && err != io.EOF {
		return "", err
	}
	buf = buf[:n]

	if n == 0 || info.Size() == 0 {
		return "empty", nil
	}

	ct := http.DetectContentType(buf)

	switch ct {
	case "application/pdf":
		return "PDF document", nil
	case "image/png":
		return "PNG image data", nil
	case "image/jpeg":
		return "JPEG image data", nil
	case "image/gif":
		return "GIF image data", nil
	case "image/webp":
		return "WebP image data", nil
	case "application/zip":
		return "Zip archive data", nil
	case "application/gzip":
		return "gzip compressed data", nil
	}

	if strings.HasPrefix(ct, "text/") || isLikelyText(buf) {
		if bytes.HasPrefix(buf, []byte("#!")) {
			return "script text executable", nil
		}
		return "ASCII/UTF-8 text", nil
	}

	if ct == "application/octet-stream" {
		return "data", nil
	}
	return ct, nil
}

func builtinFILE(args []string, stdout, stderr io.Writer) int {
	if len(args) < 2 {
		fmt.Fprintln(stderr, "usage: file PATH ...")
		return 1
	}

	paths, err := expandWildcards(args[1:])
	if err != nil {
		fmt.Fprintf(stderr, "file: glob error: %v\n", err)
		return 1
	}

	status := 0
	for _, path := range paths {
		desc, err := describeFile(path)
		if err != nil {
			fmt.Fprintf(stderr, "file: %s: %v\n", path, err)
			status = 1
			continue
		}
		fmt.Fprintf(stdout, "%s: %s\n", path, desc)
	}
	return status
}

func decodeEchoEscapes(s string) string {
	var b strings.Builder

	for i := 0; i < len(s); i++ {
		if s[i] != '\\' || i+1 >= len(s) {
			b.WriteByte(s[i])
			continue
		}

		i++
		switch s[i] {
		case 'a':
			b.WriteByte('\a')
		case 'b':
			b.WriteByte('\b')
		case 'c':
			return b.String()
		case 'e':
			b.WriteByte(0x1b)
		case 'f':
			b.WriteByte('\f')
		case 'n':
			b.WriteByte('\n')
		case 'r':
			b.WriteByte('\r')
		case 't':
			b.WriteByte('\t')
		case 'v':
			b.WriteByte('\v')
		case '\\':
			b.WriteByte('\\')
		default:
			b.WriteByte('\\')
			b.WriteByte(s[i])
		}
	}

	return b.String()
}

func builtinECHO(args []string, stdout, stderr io.Writer) int {
	noNewline := false
	enableEscapes := false
	i := 1

	for i < len(args) {
		switch args[i] {
		case "-n":
			noNewline = true
			i++
		case "-e":
			enableEscapes = true
			i++
		default:
			goto done
		}
	}

	done:
	out := strings.Join(args[i:], " ")
	if enableEscapes {
		out = decodeEchoEscapes(out)
	}

	if noNewline {
		fmt.Fprint(stdout, out)
	} else {
		fmt.Fprintln(stdout, out)
	}
	_ = stderr
	return 0
}

func addPathToTar(tw *tar.Writer, srcPath, baseName string) error {
	return filepath.Walk(srcPath, func(path string, info os.FileInfo, err error) error {
		if err != nil {
			return err
		}

		rel, err := filepath.Rel(srcPath, path)
		if err != nil {
			return err
		}

		name := baseName
		if rel != "." {
			name = filepath.Join(baseName, rel)
		}
		name = filepath.ToSlash(name)

		hdr, err := tar.FileInfoHeader(info, "")
		if err != nil {
			return err
		}
		hdr.Name = name

		if info.IsDir() && !strings.HasSuffix(hdr.Name, "/") {
			hdr.Name += "/"
		}

		if err := tw.WriteHeader(hdr); err != nil {
			return err
		}

		if info.Mode().IsRegular() {
			f, err := os.Open(path)
			if err != nil {
				return err
			}
			defer f.Close()

			if _, err := io.Copy(tw, f); err != nil {
				return err
			}
		}

		return nil
	})
}

func builtinTARGZ(args []string, stdout, stderr io.Writer) int {
	if len(args) < 3 {
		fmt.Fprintln(stderr, "usage: targz ARCHIVE.tar.gz FILE_OR_DIR ...")
		return 1
	}

	outPath := args[1]
	inputs, err := expandWildcards(args[2:])
	if err != nil {
		fmt.Fprintf(stderr, "targz: glob error: %v\n", err)
		return 1
	}
	if len(inputs) == 0 {
		fmt.Fprintln(stderr, "targz: no input files")
		return 1
	}

	outFile, err := os.Create(outPath)
	if err != nil {
		fmt.Fprintf(stderr, "targz: %s: %v\n", outPath, err)
		return 1
	}
	defer outFile.Close()

	gzw := gzip.NewWriter(outFile)
	defer gzw.Close()

	tw := tar.NewWriter(gzw)
	defer tw.Close()

	for _, in := range inputs {
		info, err := os.Lstat(in)
		if err != nil {
			fmt.Fprintf(stderr, "targz: %s: %v\n", in, err)
			return 1
		}

		base := filepath.Base(in)
		if info.IsDir() {
			if err := addPathToTar(tw, in, base); err != nil {
				fmt.Fprintf(stderr, "targz: %s: %v\n", in, err)
				return 1
			}
		} else {
			if err := addPathToTar(tw, in, base); err != nil {
				fmt.Fprintf(stderr, "targz: %s: %v\n", in, err)
				return 1
			}
		}
	}

	_ = stdout
	return 0
}

type curlConfig struct {
	method          string
	data            string
	headers         []string
	output          string
	includeHeaders  bool
	headOnly        bool
	followRedirects bool
	url             string
}

func parseCurlArgs(args []string) (*curlConfig, error) {
	cfg := &curlConfig{method: "GET"}
	i := 1

	for i < len(args) {
		switch args[i] {
		case "-X":
			if i+1 >= len(args) {
				return nil, fmt.Errorf("curl: option requires an argument -- X")
			}
			cfg.method = strings.ToUpper(args[i+1])
			i += 2
		case "-H":
			if i+1 >= len(args) {
				return nil, fmt.Errorf("curl: option requires an argument -- H")
			}
			cfg.headers = append(cfg.headers, args[i+1])
			i += 2
		case "-d", "--data":
			if i+1 >= len(args) {
				return nil, fmt.Errorf("curl: option requires an argument -- d")
			}
			cfg.data = args[i+1]
			if cfg.method == "GET" {
				cfg.method = "POST"
			}
			i += 2
		case "-o":
			if i+1 >= len(args) {
				return nil, fmt.Errorf("curl: option requires an argument -- o")
			}
			cfg.output = args[i+1]
			i += 2
		case "-i":
			cfg.includeHeaders = true
			i++
		case "-I":
			cfg.headOnly = true
			cfg.method = "HEAD"
			i++
		case "-L":
			cfg.followRedirects = true
			i++
		default:
			if strings.HasPrefix(args[i], "-") && args[i] != "-" {
				return nil, fmt.Errorf("curl: unsupported option: %s", args[i])
			}
			if cfg.url != "" {
				return nil, fmt.Errorf("curl: multiple URLs are not supported")
			}
			cfg.url = args[i]
			i++
		}
	}

	if cfg.url == "" {
		return nil, fmt.Errorf("usage: curl [-i] [-I] [-L] [-X METHOD] [-H HEADER]... [-d DATA] [-o FILE] URL")
	}
	return cfg, nil
}

func writeResponseHeaders(w io.Writer, resp *http.Response) {
	fmt.Fprintf(w, "%s %s\r\n", resp.Proto, resp.Status)
	keys := make([]string, 0, len(resp.Header))
	for k := range resp.Header {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	for _, k := range keys {
		for _, v := range resp.Header[k] {
			fmt.Fprintf(w, "%s: %s\r\n", k, v)
		}
	}
	fmt.Fprint(w, "\r\n")
}

func builtinIFCONFIG(stdout, stderr io.Writer) int {
	dns := "none"
	if addrs, err := net.LookupHost(""); err == nil && len(addrs) > 0 {
		dns = addrs[0]
	}
	fmt.Fprintf(stdout, "DNS: %s\n", dns)

	gw := "none"
	fmt.Fprintf(stdout, "Gateway: %s\n", gw)

	ifaces, _ := net.Interfaces()
	for _, i := range ifaces {
		if i.Flags&(net.FlagUp|net.FlagLoopback) != net.FlagUp { continue }
		fmt.Fprintf(stdout, "Interface: %s\nMAC: %s\n", i.Name, i.HardwareAddr)
		if addrs, err := i.Addrs(); err == nil && len(addrs) > 0 {
			for _, a := range addrs {
				if ipnet, ok := a.(*net.IPNet); ok && ipnet.IP.To4() != nil {
					fmt.Fprintf(stdout, "IPv4: %s\nMask: %s\n\n", ipnet.IP, net.IP(ipnet.Mask).String())
					break
				}
			}
		}
	}
	return 0
}

func builtinCURL(args []string, stdin io.Reader, stdout, stderr io.Writer) int {
	cfg, err := parseCurlArgs(args)
	if err != nil {
		fmt.Fprintln(stderr, err)
		return 1
	}

	var body io.Reader
	if cfg.data != "" {
		body = strings.NewReader(cfg.data)
	}

	req, err := http.NewRequest(cfg.method, cfg.url, body)
	if err != nil {
		fmt.Fprintf(stderr, "curl: %v\n", err)
		return 1
	}

	for _, h := range cfg.headers {
		parts := strings.SplitN(h, ":", 2)
		if len(parts) != 2 {
			fmt.Fprintf(stderr, "curl: invalid header: %s\n", h)
			return 1
		}
		req.Header.Add(strings.TrimSpace(parts[0]), strings.TrimSpace(parts[1]))
	}

	if cfg.data != "" && req.Header.Get("Content-Type") == "" {
		req.Header.Set("Content-Type", "application/x-www-form-urlencoded")
	}

	client := &http.Client{}
	if !cfg.followRedirects {
		client.CheckRedirect = func(req *http.Request, via []*http.Request) error {
			return http.ErrUseLastResponse
		}
	}

	resp, err := client.Do(req)
	if err != nil {
		fmt.Fprintf(stderr, "curl: %v\n", err)
		return 1
	}
	defer resp.Body.Close()

	var out io.Writer = stdout
	var outFile *os.File
	if cfg.output != "" {
		outFile, err = os.Create(cfg.output)
		if err != nil {
			fmt.Fprintf(stderr, "curl: %s: %v\n", cfg.output, err)
			return 1
		}
		defer outFile.Close()
		out = outFile
	}

	if cfg.includeHeaders || cfg.headOnly {
		writeResponseHeaders(stdout, resp)
	}

	if !cfg.headOnly {
		if _, err := io.Copy(out, resp.Body); err != nil {
			fmt.Fprintf(stderr, "curl: %v\n", err)
			return 1
		}
	}

	_ = stdin
	return 0
}

type mathParser struct {
	s string
	i int
}

func (p *mathParser) skipSpaces() {
	for p.i < len(p.s) && unicode.IsSpace(rune(p.s[p.i])) {
		p.i++
	}
}

func (p *mathParser) consume(ch byte) bool {
	p.skipSpaces()
	if p.i < len(p.s) && p.s[p.i] == ch {
		p.i++
		return true
	}
	return false
}

func (p *mathParser) parseNumber() (float64, error) {
	p.skipSpaces()
	start := p.i

	if p.i+1 < len(p.s) && p.s[p.i] == '0' && (p.s[p.i+1] == 'x' || p.s[p.i+1] == 'X') {
		p.i += 2
		hexStart := p.i
		for p.i < len(p.s) {
			c := p.s[p.i]
			if (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F') {
				p.i++
			} else {
				break
			}
		}
		if p.i == hexStart {
			return 0, fmt.Errorf("invalid hexadecimal literal")
		}
		v, err := strconv.ParseInt(p.s[start:p.i], 0, 64)
		if err != nil {
			return 0, err
		}
		return float64(v), nil
	}

	dotSeen := false
	for p.i < len(p.s) {
		c := p.s[p.i]
		if c >= '0' && c <= '9' {
			p.i++
			continue
		}
		if c == '.' && !dotSeen {
			dotSeen = true
			p.i++
			continue
		}
		break
	}

	if start == p.i {
		return 0, fmt.Errorf("number expected at position %d", p.i)
	}

	v, err := strconv.ParseFloat(p.s[start:p.i], 64)
	if err != nil {
		return 0, err
	}
	return v, nil
}

func (p *mathParser) parseFactor() (float64, error) {
	p.skipSpaces()

	if p.consume('+') {
		return p.parseFactor()
	}
	if p.consume('-') {
		v, err := p.parseFactor()
		return -v, err
	}
	if p.consume('(') {
		v, err := p.parseExpr()
		if err != nil {
			return 0, err
		}
		if !p.consume(')') {
			return 0, fmt.Errorf("missing closing parenthesis")
		}
		return v, nil
	}

	return p.parseNumber()
}

func (p *mathParser) parseTerm() (float64, error) {
	v, err := p.parseFactor()
	if err != nil {
		return 0, err
	}

	for {
		p.skipSpaces()
		switch {
		case p.consume('*'):
			rhs, err := p.parseFactor()
			if err != nil {
				return 0, err
			}
			v *= rhs
		case p.consume('/'):
			rhs, err := p.parseFactor()
			if err != nil {
				return 0, err
			}
			if rhs == 0 {
				return 0, fmt.Errorf("division by zero")
			}
			v /= rhs
		case p.consume('%'):
			rhs, err := p.parseFactor()
			if err != nil {
				return 0, err
			}
			if rhs == 0 {
				return 0, fmt.Errorf("modulo by zero")
			}
			v = math.Mod(v, rhs)
		default:
			return v, nil
		}
	}
}

func (p *mathParser) parseExpr() (float64, error) {
	v, err := p.parseTerm()
	if err != nil {
		return 0, err
	}

	for {
		p.skipSpaces()
		switch {
		case p.consume('+'):
			rhs, err := p.parseTerm()
			if err != nil {
				return 0, err
			}
			v += rhs
		case p.consume('-'):
			rhs, err := p.parseTerm()
			if err != nil {
				return 0, err
			}
			v -= rhs
		default:
			return v, nil
		}
	}
}

func evalMathExpr(expr string) (float64, error) {
	p := &mathParser{s: expr}
	v, err := p.parseExpr()
	if err != nil {
		return 0, err
	}
	p.skipSpaces()
	if p.i != len(p.s) {
		return 0, fmt.Errorf("unexpected token near: %s", p.s[p.i:])
	}
	return v, nil
}

func roundToScale(v float64, scale int) float64 {
	if scale < 0 {
		return v
	}
	f := math.Pow10(scale)
	return math.Round(v*f) / f
}

func truncateToScale(v float64, scale int) float64 {
	if scale < 0 {
		return v
	}
	f := math.Pow10(scale)
	return math.Trunc(v*f) / f
}

func formatMathResult(v float64, scale int, base string) (string, error) {
	switch base {
	case "", "10":
		if scale == 0 {
			return fmt.Sprintf("%.0f", truncateToScale(v, 0)), nil
		}
		if scale > 0 {
			return fmt.Sprintf("%.*f", scale, roundToScale(v, scale)), nil
		}
		return strconv.FormatFloat(v, 'f', -1, 64), nil
	case "16", "hex":
		if scale != 0 {
			return "", fmt.Errorf("math: base 16 requires scale 0")
		}
		return fmt.Sprintf("0x%x", int64(math.Trunc(v))), nil
	case "8", "octal":
		if scale != 0 {
			return "", fmt.Errorf("math: base 8 requires scale 0")
		}
		return fmt.Sprintf("0%o", int64(math.Trunc(v))), nil
	default:
		return "", fmt.Errorf("math: unsupported base: %s", base)
	}
}

func builtinMATH(args []string, stdout, stderr io.Writer) int {
	scale := 6
	base := "10"
	var exprParts []string

	i := 1
	for i < len(args) {
		switch args[i] {
		case "-s", "--scale":
			if i+1 >= len(args) {
				fmt.Fprintln(stderr, "math: option requires an argument -- scale")
				return 1
			}
			if args[i+1] == "max" {
				scale = -1
			} else {
				n, err := strconv.Atoi(args[i+1])
				if err != nil || n < 0 {
					fmt.Fprintf(stderr, "math: invalid scale: %s\n", args[i+1])
					return 1
				}
				scale = n
			}
			i += 2
		case "-b", "--base":
			if i+1 >= len(args) {
				fmt.Fprintln(stderr, "math: option requires an argument -- base")
				return 1
			}
			base = strings.ToLower(args[i+1])
			i += 2
		case "-h", "--help":
			fmt.Fprintln(stdout, "usage: math [(-s|--scale) N] [(-b|--base) BASE] EXPRESSION ...")
			fmt.Fprintln(stdout, "BASE: 10, 16/hex, 8/octal")
			return 0
		default:
			exprParts = append(exprParts, args[i])
			i++
		}
	}

	if len(exprParts) == 0 {
		fmt.Fprintln(stderr, "usage: math [(-s|--scale) N] [(-b|--base) BASE] EXPRESSION ...")
		return 1
	}

	expr := strings.Join(exprParts, " ")
	v, err := evalMathExpr(expr)
	if err != nil {
		fmt.Fprintf(stderr, "math: %v\n", err)
		return 1
	}

	out, err := formatMathResult(v, scale, base)
	if err != nil {
		fmt.Fprintln(stderr, err)
		return 1
	}

	fmt.Fprintln(stdout, out)
	return 0
}

func builtinCAL(args []string, stdout, stderr io.Writer) int {
	now := time.Now()
	year := now.Year()
	month := now.Month()

	switch len(args) {
	case 1:
	case 2:
		y, err := strconv.Atoi(args[1])
		if err != nil {
			fmt.Fprintf(stderr, "cal: invalid year '%s'\n", args[1])
			return 1
		}
		year = y
	case 3:
		y, err := strconv.Atoi(args[1])
		if err != nil {
			fmt.Fprintf(stderr, "cal: invalid year '%s'\n", args[1])
			return 1
		}
		year = y
		m, err := strconv.Atoi(args[2])
		if err != nil || m < 1 || m > 12 {
			fmt.Fprintf(stderr, "cal: invalid month '%s'\n", args[2])
			return 1
		}
		month = time.Month(m)
	default:
		fmt.Fprintln(stderr, "usage: cal [YEAR [MONTH]]")
		return 1
	}

	t := time.Date(year, month, 1, 0, 0, 0, 0, time.UTC)
	firstWeekday := int(t.Weekday())
	daysInMonth := int(t.AddDate(0, 1, -1).Day())

	fmt.Fprintf(stdout, "     %s %d\n", now.Format("Jan"), year)
	fmt.Fprintln(stdout, "  Su Mo Tu We Th Fr Sa")

	line := strings.Repeat("   ", firstWeekday)
	for day := 1; day <= daysInMonth; day++ {
		today := now.Year() == year && now.Month() == month && now.Day() == day
		color := ""
		reset := ""
		if today && isTerminalWriter(stdout) {
			color = colorToday
			reset = colorOff
		}
		line += fmt.Sprintf("%s%2d%s ", color, day, reset)
		if len(line) >= 21 {
			fmt.Fprintln(stdout, line[:21])
			line = ""
		}
	}
	if len(line) > 0 {
		fmt.Fprintln(stdout, line[:21])
	}

	return 0
}

func builtinHash(args []string, stdin io.Reader, stdout, stderr io.Writer, newHash func() hash.Hash) int {
	if len(args) < 2 {
		fmt.Fprintln(stderr, "usage: hashcmd FILE ...")
		return 1
	}

	files, err := expandWildcards(args[1:])
	if err != nil {
		fmt.Fprintf(stderr, "hashcmd: glob error: %v\n", err)
		return 1
	}

	status := 0
	for _, file := range files {
		f, err := os.Open(file)
		if err != nil {
			fmt.Fprintf(stderr, "hashcmd: %s: %v\n", file, err)
			status = 1
			continue
		}

		h := newHash()
		_, copyErr := io.Copy(h, f)
		_ = f.Close()
		if copyErr != nil {
			fmt.Fprintf(stderr, "hashcmd: %s: %v\n", file, copyErr)
			status = 1
			continue
		}

		fmt.Fprintf(stdout, "%s  %s\n", hex.EncodeToString(h.Sum(nil)), file)
	}

	return status
}

func builtinVERSION(stdout io.Writer) int {
	fmt.Fprintf(stdout, "Gsh (Unix-like shell) version %s\n", Version)
	return 0
}

func builtinHELP(args []string, stdout, stderr io.Writer) int {
	if len(args) == 1 {
		names := make([]string, len(builtinNames))
		copy(names, builtinNames)
		sort.Strings(names)

		fmt.Fprintln(stdout, "Built-in commands:")
		for _, name := range names {
			fmt.Fprintf(stdout, "  %s\n", name)
		}
		fmt.Fprintln(stdout)
		fmt.Fprintln(stdout, "Use 'help COMMAND' for a short description.")
		return 0
	}

	status := 0
	for _, name := range args[1:] {
		msg, ok := builtinHelp[name]
		if !ok {
			fmt.Fprintf(stderr, "help: no such built-in command: %s\n", name)
			status = 1
			continue
		}
		fmt.Fprintln(stdout, msg)
	}
	return status
}

func isBuiltin(cmd string) bool {
	switch cmd {
		case "cd", "pwd", "ls", "cat", "grep", "touch",
		"nc", "wc", "uniq", "cp", "mv", "rm",
		"rmdir", "mkdir", "history", "head", "tail",
		"cut", "sort", "more", "file", "echo", "targz",
		"md5", "sha256", "sha512",
		"curl", "math", "cal", "help", "exit":
		return true
	default:
		return false
	}
}

func runBuiltin(args []string, hist *History, stdin io.Reader, stdout, stderr io.Writer) int {
	switch args[0] {
	case "cd":
		return builtinCD(args, stdout, stderr)
	case "pwd":
		return builtinPWD(stdout, stderr)
	case "ls":
		return builtinLS(args, stdout, stderr)
	case "cat":
		return builtinCAT(args, stdin, stdout, stderr)
	case "grep":
		return builtinGREP(args, stdin, stdout, stderr)
	case "touch":
		return builtinTOUCH(args, stdout, stderr)
	case "nc":
		return builtinNC(args, stdin, stdout, stderr)
	case "wc":
		return builtinWC(args, stdin, stdout, stderr)
	case "uniq":
		return builtinUNIQ(args, stdin, stdout, stderr)
	case "cp":
		return builtinCP(args, stdout, stderr)
	case "mv":
		return builtinMV(args, stdout, stderr)
	case "rm":
		return builtinRM(args, stdout, stderr)
	case "rmdir":
		return builtinRMDIR(args, stdout, stderr)
	case "mkdir":
		return builtinMKDIR(args, stdout, stderr)
	case "history":
		return builtinHISTORY(args, hist, stdout, stderr)
	case "head":
		return builtinHEAD(args, stdin, stdout, stderr)
	case "tail":
		return builtinTAIL(args, stdin, stdout, stderr)
	case "cut":
		return builtinCUT(args, stdin, stdout, stderr)
	case "sort":
		return builtinSORT(args, stdin, stdout, stderr)
	case "more":
		return builtinMORE(args, stdin, stdout, stderr)
	case "file":
		return builtinFILE(args, stdout, stderr)
	case "echo":
		return builtinECHO(args, stdout, stderr)
	case "targz":
		return builtinTARGZ(args, stdout, stderr)
	case "md5":
		return builtinHash(args, stdin, stdout, stderr, md5.New)
	case "sha256":
		return builtinHash(args, stdin, stdout, stderr, sha256.New)
	case "sha512":
		return builtinHash(args, stdin, stdout, stderr, sha512.New)
	case "ifconfig":
		return builtinIFCONFIG(stdout, stderr)
	case "curl":
		return builtinCURL(args, stdin, stdout, stderr)
	case "math":
		return builtinMATH(args, stdout, stderr)
	case "cal":
		return builtinCAL(args, stdout, stderr)
	case "version":
		return builtinVERSION(stdout)
	case "help":
		return builtinHELP(args, stdout, stderr)
	case "exit":
		fmt.Fprintln(stdout, "bye")
		os.Exit(0)
	}
	return 1
}

func runExternal(args []string, stdin io.Reader, stdout, stderr io.Writer) int {
	expandedArgs, err := expandWildcards(args)
	if err != nil {
		fmt.Fprintf(stderr, "glob error: %v\n", err)
		return 1
	}
	if len(expandedArgs) == 0 {
		return 0
	}

	cmd := exec.Command(expandedArgs[0], expandedArgs[1:]...)
	cmd.Stdin = stdin
	cmd.Stdout = stdout
	cmd.Stderr = stderr

	if err := cmd.Run(); err != nil {
		fmt.Fprintf(stderr, "error: %v\n", err)
		return 1
	}
	return 0
}

func openInputFile(path string) (*os.File, error) {
	return os.Open(path)
}

func openOutputFile(path string, appendMode bool) (*os.File, error) {
	flag := os.O_CREATE | os.O_WRONLY
	if appendMode {
		flag |= os.O_APPEND
	} else {
		flag |= os.O_TRUNC
	}
	return os.OpenFile(path, flag, 0644)
}

func runSingleCommand(cmd Command, hist *History, stdin io.Reader, stdout, stderr io.Writer) int {
	var in io.Reader = stdin
	var out io.Writer = stdout
	var inputFile *os.File
	var outputFile *os.File

	if cmd.Input != "" {
		f, err := openInputFile(cmd.Input)
		if err != nil {
			fmt.Fprintf(stderr, "%s: %v\n", cmd.Input, err)
			return 1
		}
		inputFile = f
		in = f
		defer inputFile.Close()
	}

	if cmd.Output != "" {
		f, err := openOutputFile(cmd.Output, cmd.Append)
		if err != nil {
			fmt.Fprintf(stderr, "%s: %v\n", cmd.Output, err)
			return 1
		}
		outputFile = f
		out = f
		defer outputFile.Close()
	}

	if len(cmd.Args) == 0 {
		return 0
	}

	if isBuiltin(cmd.Args[0]) {
		return runBuiltin(cmd.Args, hist, in, out, stderr)
	}
	return runExternal(cmd.Args, in, out, stderr)
}

func runPipeline(p *Pipeline, hist *History) int {
	if p == nil || len(p.Commands) == 0 {
		return 0
	}

	if len(p.Commands) == 1 {
		return runSingleCommand(p.Commands[0], hist, os.Stdin, os.Stdout, os.Stderr)
	}

	var readers []*io.PipeReader
	var writers []*io.PipeWriter
	for i := 0; i < len(p.Commands)-1; i++ {
		pr, pw := io.Pipe()
		readers = append(readers, pr)
		writers = append(writers, pw)
	}

	statusCh := make(chan int, len(p.Commands))

	for i, c := range p.Commands {
		var in io.Reader = os.Stdin
		var out io.Writer = os.Stdout

		if i > 0 {
			in = readers[i-1]
		}
		if i < len(p.Commands)-1 {
			out = writers[i]
		}

		go func(idx int, cmd Command, stdin io.Reader, stdout io.Writer) {
			status := runSingleCommand(cmd, hist, stdin, stdout, os.Stderr)

			if idx > 0 {
				if r, ok := stdin.(*io.PipeReader); ok {
					_ = r.Close()
				}
			}
			if idx < len(p.Commands)-1 {
				if w, ok := stdout.(*io.PipeWriter); ok {
					_ = w.Close()
				}
			}
			statusCh <- status
		}(i, c, in, out)
	}

	status := 0
	for i := 0; i < len(p.Commands); i++ {
		s := <-statusCh
		if s != 0 {
			status = s
		}
	}
	return status
}

func runLine(line string, hist *History) int {
	line = strings.TrimSpace(line)
	if line == "" {
		return 0
	}

	p, err := parsePipeline(line)
	if err != nil {
		fmt.Fprintf(os.Stderr, "parse error: %v\n", err)
		return 1
	}
	return runPipeline(p, hist)
}

func main() {
	fd := int(os.Stdin.Fd())
	if !term.IsTerminal(fd) {
		fmt.Fprintln(os.Stderr, "stdin is not a terminal")
		os.Exit(1)
	}

	oldState, err := term.MakeRaw(fd)
	if err != nil {
		fmt.Fprintf(os.Stderr, "failed to set raw mode: %v\n", err)
		os.Exit(1)
	}
	defer term.Restore(fd, oldState)

	editor := &Editor{}
	history := NewHistory()
	printPrompt()

	for {
		key, err := readKey(os.Stdin)
		if err != nil {
			if err == io.EOF {
				fmt.Println()
				return
			}
			fmt.Fprintf(os.Stderr, "\nread error: %v\n", err)
			return
		}

		switch {
		case len(key) == 1 && key[0] == 0x01:
			editor.moveHome()
			editor.refresh(os.Stdout)

		case len(key) == 1 && key[0] == 0x05:
			editor.moveEnd()
			editor.refresh(os.Stdout)

		case len(key) == 1 && key[0] == 0x08:
			history.ResetNavigation()
			editor.backspace()
			editor.refresh(os.Stdout)

		case len(key) == 1 && key[0] == 0x0b:
			editor.killToEnd()
			editor.refresh(os.Stdout)

		case len(key) == 1 && key[0] == 0x0c:
			clearScreen(os.Stdout)
			editor.refresh(os.Stdout)

		case len(key) == 1 && key[0] == 0x0e:
			if line, ok := history.Next(); ok {
				editor.setLine(line)
				editor.refresh(os.Stdout)
			}

		case len(key) == 1 && key[0] == 0x10:
			if line, ok := history.Prev(editor.line()); ok {
				editor.setLine(line)
				editor.refresh(os.Stdout)
			}

		case len(key) == 1 && key[0] == 0x15:
			editor.killToStart()
			editor.refresh(os.Stdout)

		case len(key) == 1 && key[0] == 0x17:
			editor.killPrevWord()
			editor.refresh(os.Stdout)

		case len(key) == 1 && key[0] == 0x19:
			editor.yankText()
			editor.refresh(os.Stdout)

		case len(key) == 1 && key[0] == 0x7f:
			history.ResetNavigation()
			editor.backspace()
			editor.refresh(os.Stdout)

		case len(key) == 1 && key[0] == 0x04:
			if len(editor.buf) == 0 {
				fmt.Println()
				return
			}

		case len(key) == 1 && key[0] == 0x09:
			completeAtCursor(editor)
			editor.refresh(os.Stdout)

		case len(key) == 1 && (key[0] == '\r' || key[0] == '\n'):
			line := editor.line()
			fmt.Print("\r\n")
			_ = runLine(line, history)
			history.Add(line)
			editor.clear()
			printPrompt()

		case len(key) == 3 && key[0] == 0x1b && key[1] == '[' && key[2] == 'D':
			editor.moveLeft()
			editor.refresh(os.Stdout)

		case len(key) == 3 && key[0] == 0x1b && key[1] == '[' && key[2] == 'C':
			editor.moveRight()
			editor.refresh(os.Stdout)

		case len(key) == 1 && key[0] >= 0x20 && key[0] <= 0x7e:
			history.ResetNavigation()
			editor.insertRune(rune(key[0]))
			editor.refresh(os.Stdout)
		}
	}
}
