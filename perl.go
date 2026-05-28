/*
* Last Changed: 2026-05-29 Fri 05:50:15
*/

package main

import (
	"fmt"
	"io"
	"os"
	"strings"
)

func builtinMPERL(args []string, stdin io.Reader, stdout, stderr io.Writer) int {
	if len(args) == 1 {
		if _, err := io.Copy(stdout, stdin); err != nil {
			fmt.Fprintf(stderr, "mperl: stdin: %v\n", err)
			return 1
		}
		return 0
	}

	var rawFiles []string
	for _, a := range args[1:] {
		if strings.HasPrefix(a, "-") && a != "-" {
			fmt.Fprintf(stderr, "mperl: unsupported option %s\n", a)
			fmt.Fprintln(stderr, "usage: mperl [FILE ...]")
			return 1
		}
		rawFiles = append(rawFiles, a)
	}

	files, err := expandWildcards(rawFiles)
	if err != nil {
		fmt.Fprintf(stderr, "mperl: glob error: %v\n", err)
		return 1
	}

	if len(files) == 0 {
		return 0
	}

	status := 0
	for _, file := range files {
		if file == "-" {
			if _, err := io.Copy(stdout, stdin); err != nil {
				fmt.Fprintf(stderr, "mperl: stdin: %v\n", err)
				status = 1
			}
			continue
		}

		f, err := os.Open(file)
		if err != nil {
			fmt.Fprintf(stderr, "mperl: %s: %v\n", file, err)
			status = 1
			continue
		}

		_, err = io.Copy(stdout, f)
		_ = f.Close()
		if err != nil {
			fmt.Fprintf(stderr, "mperl: %s: %v\n", file, err)
			status = 1
		}
	}

	return status
}
