// Copyright 2016 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// This file implements source, a buffered rune reader
// specialized for scanning Go code: Reading
// ASCII characters, maintaining current (line, col)
// position information, and recording of the most
// recently read source segment are highly optimized.
// This file is self-contained (go tool compile source.go
// compiles) and thus could be made into its own package.

package syntax

import (
	"unicode/utf8"
)

type spos struct {
	offset    int  // byte offset into file
	line, col uint // line, column (1-based)
}

type source struct {
	errh func(pos spos, msg string)

	buf  string
	b    int  // buffer index for start of active segment, or -1 if none
	r    int  // buffer index of ch
	line uint // source position of ch (0-based)
	bol  int  // buffer index for beginning of current line
	ch   rune // most recently read character
	chw  int  // width of ch
}

func (s *source) init(in string, errh func(pos spos, msg string)) {
	s.buf = in
	s.errh = errh

	s.b = -1
	s.r = 0
	s.line = 0
	s.bol = 0
	s.ch = ' '
	s.chw = 0
}

// starting points for line and column numbers
const linebase = 1
const colbase = 1

// pos returns the (line, col) source position of s.ch.
func (s *source) pos() spos {
	return spos{s.r, linebase + s.line, colbase + uint(s.r-s.bol)}
}

// error reports the error msg at source position s.pos().
func (s *source) error(msg string) {
	s.errh(s.pos(), msg)
}

// start starts a new active source segment (including s.ch).
// As long as stop has not been called, the active segment's
// bytes (excluding s.ch) may be retrieved by calling segment.
func (s *source) start()          { s.b = s.r }
func (s *source) stop()           { s.b = -1 }
func (s *source) segment() string { return s.buf[s.b:s.r] }

// rewind rewinds the scanner's read position and character s.ch
// to the start of the currently active segment, which must not
// contain any newlines (otherwise position information will be
// incorrect). Currently, rewind is only needed for handling the
// source sequence ".."; it must not be called outside an active
// segment.
func (s *source) rewind() {
	// ok to verify precondition - rewind is rarely called
	if s.b < 0 {
		panic("no active segment")
	}
	s.r = s.b
	s.chw = 0
	s.nextch()
}

func (s *source) nextch() {
redo:
	s.r += s.chw
	if s.ch == '\n' {
		s.line++
		s.bol = s.r
	}

	// EOF
	if s.r >= len(s.buf) {
		s.ch = -1
		s.chw = 0
		return
	}

	// fast common case: at least one ASCII character
	if s.buf[s.r] < utf8.RuneSelf {
		s.ch = rune(s.buf[s.r])
		s.chw = 1
		if s.ch == 0 {
			s.error("invalid NUL character")
			goto redo
		}
		return
	}

	s.ch, s.chw = utf8.DecodeRuneInString(s.buf[s.r:])

	if s.ch == utf8.RuneError && s.chw == 1 {
		s.error("invalid UTF-8 encoding")
		goto redo
	}

	// BOM's are only allowed as the first character in a file
	const BOM = 0xfeff
	if s.ch == BOM {
		if s.r > 0 {
			s.error("invalid BOM in the middle of the file")
		}
		goto redo
	}
}
