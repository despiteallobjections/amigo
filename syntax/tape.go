// Copyright 2022 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package syntax

import "io"

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
	errh func(line, col uint, msg string)

	tape    []tapeelem
	tapepos int

	tapeelem
}

func (s *tapescanner) init(src io.Reader, errh func(line, col uint, msg string), mode uint) {
	s.errh = errh

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
		s.errh(s.line, s.col, s.lit)
		goto again
	}
}
