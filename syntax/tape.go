// Copyright 2022 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package syntax

import (
	"io"
	"strconv"
	"strings"
)

type tapeelem struct {
	// current token, valid after calling next()
	line, col uint
	blank     bool // line is blank up to col
	tok       token
	lit       string   // valid if tok is _Name, _Literal, or _Semi ("semicolon", "newline", or "EOF"); may be malformed if bad is true
	bad       bool     // valid if tok is _Literal, true if a syntax error occurred, lit may be malformed
	kind      LitKind  // valid if tok is _Literal
	op        Operator // valid if tok is _Operator, _AssignOp, or _IncOp
	prec      int      // valid if tok is _Operator, _AssignOp, or _IncOp
}

type tapescanner struct {
	tape    []tapeelem
	tapepos int

	tapeelem

	file   *PosBase
	errh   ErrorHandler
	pragh  PragmaHandler
	pragma Pragma // pragmas

	base   *PosBase // current position base
	first  error    // first error encountered
	errcnt int      // number of errors encountered
}

func (s *tapescanner) init(src io.Reader, mode uint) {
	s.tape = nil
	s.tapepos = 0

	var old scanner
	old.init(src, func(line, col uint, msg string) {
		s.tape = append(s.tape, tapeelem{line: line, col: col, tok: _Error, lit: msg})
	}, mode)

	for {
		old.next()
		s.tape = append(s.tape, old.tapeelem)
		if old.tok == _EOF {
			break
		}
	}
}

func (s *tapescanner) next() {
again:
	s.tapeelem = s.tape[s.tapepos]
	s.tapepos++

	if s.tok == _Error {
		s.errh0(s.line, s.col, s.lit)
		goto again
	}
}

// Error and directive handler for scanner.
// Because the (line, col) positions passed to the
// handler is always at or after the current reading
// position, it is safe to use the most recent position
// base to compute the corresponding Pos value.
func (s *tapescanner) errh0(line, col uint, msg string) {
	if msg[0] != '/' {
		s.errorAt(s.posAt(line, col), msg)
		return
	}

	// otherwise it must be a comment containing a line or go: directive.
	// //line directives must be at the start of the line (column colbase).
	// /*line*/ directives can be anywhere in the line.
	text := commentText(msg)
	if (col == colbase || msg[1] == '*') && strings.HasPrefix(text, "line ") {
		var pos Pos // position immediately following the comment
		if msg[1] == '/' {
			// line comment (newline is part of the comment)
			pos = MakePos(s.file, line+1, colbase)
		} else {
			// regular comment
			// (if the comment spans multiple lines it's not
			// a valid line directive and will be discarded
			// by updateBase)
			pos = MakePos(s.file, line, col+uint(len(msg)))
		}
		s.updateBase(pos, line, col+2+5, text[5:]) // +2 to skip over // or /*
		return
	}

	// go: directive (but be conservative and test)
	if s.pragh != nil && strings.HasPrefix(text, "go:") {
		s.pragma = s.pragh(s.posAt(line, col+2), s.blank, text, s.pragma) // +2 to skip over // or /*
	}
}

// posAt returns the Pos value for (line, col) and the current position base.
func (s *tapescanner) posAt(line, col uint) Pos {
	return MakePos(s.base, line, col)
}

// error reports an error at the given position.
func (s *tapescanner) errorAt(pos Pos, msg string) {
	err := Error{pos, msg}
	if s.first == nil {
		s.first = err
	}
	s.errcnt++
	if s.errh == nil {
		panic(s.first)
	}
	s.errh(err)
}

// updateBase sets the current position base to a new line base at pos.
// The base's filename, line, and column values are extracted from text
// which is positioned at (tline, tcol) (only needed for error messages).
func (p *tapescanner) updateBase(pos Pos, tline, tcol uint, text string) {
	i, n, ok := trailingDigits(text)
	if i == 0 {
		return // ignore (not a line directive)
	}
	// i > 0

	if !ok {
		// text has a suffix :xxx but xxx is not a number
		p.errorAt(p.posAt(tline, tcol+i), "invalid line number: "+text[i:])
		return
	}

	var line, col uint
	i2, n2, ok2 := trailingDigits(text[:i-1])
	if ok2 {
		//line filename:line:col
		i, i2 = i2, i
		line, col = n2, n
		if col == 0 || col > PosMax {
			p.errorAt(p.posAt(tline, tcol+i2), "invalid column number: "+text[i2:])
			return
		}
		text = text[:i2-1] // lop off ":col"
	} else {
		//line filename:line
		line = n
	}

	if line == 0 || line > PosMax {
		p.errorAt(p.posAt(tline, tcol+i), "invalid line number: "+text[i:])
		return
	}

	// If we have a column (//line filename:line:col form),
	// an empty filename means to use the previous filename.
	filename := text[:i-1] // lop off ":line"
	trimmed := false
	if filename == "" && ok2 {
		filename = p.base.Filename()
		trimmed = p.base.Trimmed()
	}

	p.base = NewLineBase(pos, filename, trimmed, line, col)
}

func commentText(s string) string {
	if s[:2] == "/*" {
		return s[2 : len(s)-2] // lop off /* and */
	}

	// line comment (does not include newline)
	// (on Windows, the line comment may end in \r\n)
	i := len(s)
	if s[i-1] == '\r' {
		i--
	}
	return s[2:i] // lop off //, and \r at end, if any
}

func trailingDigits(text string) (uint, uint, bool) {
	// Want to use LastIndexByte below but it's not defined in Go1.4 and bootstrap fails.
	i := strings.LastIndex(text, ":") // look from right (Windows filenames may contain ':')
	if i < 0 {
		return 0, 0, false // no ":"
	}
	// i >= 0
	n, err := strconv.ParseUint(text[i+1:], 10, 0)
	return uint(i + 1), uint(n), err == nil
}
