// Copyright 2016 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// This file implements scanner, a lexical tokenizer for
// Go source. After initialization, consecutive calls of
// next advance the scanner one token at a time.
//
// This file, source.go, tokens.go, and token_string.go are self-contained
// (`go tool compile scanner.go source.go tokens.go token_string.go` compiles)
// and thus could be made into their own package.

package syntax

import (
	"fmt"
	"io"
	"unicode"
	"unicode/utf8"
)

// The mode flags below control which comments are reported
// by calling the error handler. If no flag is set, comments
// are ignored.
const (
	comments   uint = 1 << iota // call handler for all comments
	directives                  // call handler for directives only
)

type scanner struct {
	source source
	mode   uint
	nlsemi bool // if set '\n' and EOF translate to ';'

	// current token, valid after calling next()
	tapeelem
}

func (s *scanner) init(src string, errh func(line, col uint, msg string), mode uint) {
	s.source.init(src, errh)
	s.mode = mode
	s.nlsemi = false
}

// Deprecated: Use init instead.
func (s *scanner) initReader(src io.Reader, errh func(line, col uint, msg string), mode uint) {
	s.init(readAllString(src), errh, mode)
}

func readAllString(src io.Reader) string {
	buf, err := io.ReadAll(src)
	if err != nil {
		panic(err) // TODO(mdempsky): Proper error handling.
	}
	return string(buf)
}

// errorf reports an error at the most recently read character position.
func (s *scanner) errorf(format string, args ...interface{}) {
	s.source.error(fmt.Sprintf(format, args...))
}

// errorAtf reports an error at a byte column offset relative to the current token start.
func (s *scanner) errorAtf(offset int, format string, args ...interface{}) {
	s.source.errh(s.line, s.col+uint(offset), fmt.Sprintf(format, args...))
}

// setLit sets the scanner state for a recognized _Literal token.
func (s *scanner) setLit(kind LitKind, ok bool) {
	s.nlsemi = true
	s.tok = _Literal
	s.lit = s.source.segment()
	s.bad = !ok
	s.kind = kind
}

// next advances the scanner by reading the next token.
//
// If a read, source encoding, or lexical error occurs, next calls
// the installed error handler with the respective error position
// and message. The error message is guaranteed to be non-empty and
// never starts with a '/'. The error handler must exist.
//
// If the scanner mode includes the comments flag and a comment
// (including comments containing directives) is encountered, the
// error handler is also called with each comment position and text
// (including opening /* or // and closing */, but without a newline
// at the end of line comments). Comment text always starts with a /
// which can be used to distinguish these handler calls from errors.
//
// If the scanner mode includes the directives (but not the comments)
// flag, only comments containing a //line, /*line, or //go: directive
// are reported, in the same way as regular comments.
func (s *scanner) next() {
	nlsemi := s.nlsemi
	s.nlsemi = false

redo:
	// skip white space
	s.source.stop()
	startLine, startCol := s.source.pos()
	for s.source.ch == ' ' || s.source.ch == '\t' || s.source.ch == '\n' && !nlsemi || s.source.ch == '\r' {
		s.source.nextch()
	}

	// token start
	s.line, s.col = s.source.pos()
	s.blank = s.line > startLine || startCol == colbase
	s.source.start()
	if isLetter(s.source.ch) || s.source.ch >= utf8.RuneSelf && s.atIdentChar(true) {
		s.source.nextch()
		s.ident()
		return
	}

	switch s.source.ch {
	case -1:
		if nlsemi {
			s.lit = "EOF"
			s.tok = _Semi
			break
		}
		s.tok = _EOF

	case '\n':
		s.source.nextch()
		s.lit = "newline"
		s.tok = _Semi

	case '0', '1', '2', '3', '4', '5', '6', '7', '8', '9':
		s.number(false)

	case '"':
		s.stdString()

	case '`':
		s.rawString()

	case '\'':
		s.rune()

	case '(':
		s.source.nextch()
		s.tok = _Lparen

	case '[':
		s.source.nextch()
		s.tok = _Lbrack

	case '{':
		s.source.nextch()
		s.tok = _Lbrace

	case ',':
		s.source.nextch()
		s.tok = _Comma

	case ';':
		s.source.nextch()
		s.lit = "semicolon"
		s.tok = _Semi

	case ')':
		s.source.nextch()
		s.nlsemi = true
		s.tok = _Rparen

	case ']':
		s.source.nextch()
		s.nlsemi = true
		s.tok = _Rbrack

	case '}':
		s.source.nextch()
		s.nlsemi = true
		s.tok = _Rbrace

	case ':':
		s.source.nextch()
		if s.source.ch == '=' {
			s.source.nextch()
			s.tok = _Define
			break
		}
		s.tok = _Colon

	case '.':
		s.source.nextch()
		if isDecimal(s.source.ch) {
			s.number(true)
			break
		}
		if s.source.ch == '.' {
			s.source.nextch()
			if s.source.ch == '.' {
				s.source.nextch()
				s.tok = _DotDotDot
				break
			}
			s.source.rewind() // now s.ch holds 1st '.'
			s.source.nextch() // consume 1st '.' again
		}
		s.tok = _Dot

	case '+':
		s.source.nextch()
		s.op, s.prec = Add, precAdd
		if s.source.ch != '+' {
			goto assignop
		}
		s.source.nextch()
		s.nlsemi = true
		s.tok = _IncOp

	case '-':
		s.source.nextch()
		s.op, s.prec = Sub, precAdd
		if s.source.ch != '-' {
			goto assignop
		}
		s.source.nextch()
		s.nlsemi = true
		s.tok = _IncOp

	case '*':
		s.source.nextch()
		s.op, s.prec = Mul, precMul
		// don't goto assignop - want _Star token
		if s.source.ch == '=' {
			s.source.nextch()
			s.tok = _AssignOp
			break
		}
		s.tok = _Star

	case '/':
		s.source.nextch()
		if s.source.ch == '/' {
			s.source.nextch()
			s.lineComment()
			goto redo
		}
		if s.source.ch == '*' {
			s.source.nextch()
			s.fullComment()
			if line, _ := s.source.pos(); line > s.line && nlsemi {
				// A multi-line comment acts like a newline;
				// it translates to a ';' if nlsemi is set.
				s.lit = "newline"
				s.tok = _Semi
				break
			}
			goto redo
		}
		s.op, s.prec = Div, precMul
		goto assignop

	case '%':
		s.source.nextch()
		s.op, s.prec = Rem, precMul
		goto assignop

	case '&':
		s.source.nextch()
		if s.source.ch == '&' {
			s.source.nextch()
			s.op, s.prec = AndAnd, precAndAnd
			s.tok = _Operator
			break
		}
		s.op, s.prec = And, precMul
		if s.source.ch == '^' {
			s.source.nextch()
			s.op = AndNot
		}
		goto assignop

	case '|':
		s.source.nextch()
		if s.source.ch == '|' {
			s.source.nextch()
			s.op, s.prec = OrOr, precOrOr
			s.tok = _Operator
			break
		}
		s.op, s.prec = Or, precAdd
		goto assignop

	case '^':
		s.source.nextch()
		s.op, s.prec = Xor, precAdd
		goto assignop

	case '<':
		s.source.nextch()
		if s.source.ch == '=' {
			s.source.nextch()
			s.op, s.prec = Leq, precCmp
			s.tok = _Operator
			break
		}
		if s.source.ch == '<' {
			s.source.nextch()
			s.op, s.prec = Shl, precMul
			goto assignop
		}
		if s.source.ch == '-' {
			s.source.nextch()
			s.tok = _Arrow
			break
		}
		s.op, s.prec = Lss, precCmp
		s.tok = _Operator

	case '>':
		s.source.nextch()
		if s.source.ch == '=' {
			s.source.nextch()
			s.op, s.prec = Geq, precCmp
			s.tok = _Operator
			break
		}
		if s.source.ch == '>' {
			s.source.nextch()
			s.op, s.prec = Shr, precMul
			goto assignop
		}
		s.op, s.prec = Gtr, precCmp
		s.tok = _Operator

	case '=':
		s.source.nextch()
		if s.source.ch == '=' {
			s.source.nextch()
			s.op, s.prec = Eql, precCmp
			s.tok = _Operator
			break
		}
		s.tok = _Assign

	case '!':
		s.source.nextch()
		if s.source.ch == '=' {
			s.source.nextch()
			s.op, s.prec = Neq, precCmp
			s.tok = _Operator
			break
		}
		s.op, s.prec = Not, 0
		s.tok = _Operator

	case '~':
		s.source.nextch()
		s.op, s.prec = Tilde, 0
		s.tok = _Operator

	default:
		s.errorf("invalid character %#U", s.source.ch)
		s.source.nextch()
		goto redo
	}

	return

assignop:
	if s.source.ch == '=' {
		s.source.nextch()
		s.tok = _AssignOp
		return
	}
	s.tok = _Operator
}

func (s *scanner) ident() {
	// accelerate common case (7bit ASCII)
	for isLetter(s.source.ch) || isDecimal(s.source.ch) {
		s.source.nextch()
	}

	// general case
	if s.source.ch >= utf8.RuneSelf {
		for s.atIdentChar(false) {
			s.source.nextch()
		}
	}

	// possibly a keyword
	lit := s.source.segment()
	if len(lit) >= 2 {
		if tok := keywordMap[hash(lit)]; tok != 0 && tokStrFast(tok) == lit {
			s.nlsemi = contains(1<<_Break|1<<_Continue|1<<_Fallthrough|1<<_Return, tok)
			s.tok = tok
			return
		}
	}

	s.nlsemi = true
	s.lit = lit
	s.tok = _Name
}

// tokStrFast is a faster version of token.String, which assumes that tok
// is one of the valid tokens - and can thus skip bounds checks.
func tokStrFast(tok token) string {
	return _token_name[_token_index[tok-1]:_token_index[tok]]
}

func (s *scanner) atIdentChar(first bool) bool {
	switch {
	case unicode.IsLetter(s.source.ch) || s.source.ch == '_':
		// ok
	case unicode.IsDigit(s.source.ch):
		if first {
			s.errorf("identifier cannot begin with digit %#U", s.source.ch)
		}
	case s.source.ch >= utf8.RuneSelf:
		s.errorf("invalid character %#U in identifier", s.source.ch)
	default:
		return false
	}
	return true
}

// hash is a perfect hash function for keywords.
// It assumes that s has at least length 2.
func hash(s string) uint {
	return (uint(s[0])<<4 ^ uint(s[1]) + uint(len(s))) & uint(len(keywordMap)-1)
}

var keywordMap [1 << 6]token // size must be power of two

func init() {
	// populate keywordMap
	for tok := _Break; tok <= _Var; tok++ {
		h := hash(tok.String())
		if keywordMap[h] != 0 {
			panic("imperfect hash")
		}
		keywordMap[h] = tok
	}
}

func lower(ch rune) rune     { return ('a' - 'A') | ch } // returns lower-case ch iff ch is ASCII letter
func isLetter(ch rune) bool  { return 'a' <= lower(ch) && lower(ch) <= 'z' || ch == '_' }
func isDecimal(ch rune) bool { return '0' <= ch && ch <= '9' }
func isHex(ch rune) bool     { return '0' <= ch && ch <= '9' || 'a' <= lower(ch) && lower(ch) <= 'f' }

// digits accepts the sequence { digit | '_' }.
// If base <= 10, digits accepts any decimal digit but records
// the index (relative to the literal start) of a digit >= base
// in *invalid, if *invalid < 0.
// digits returns a bitset describing whether the sequence contained
// digits (bit 0 is set), or separators '_' (bit 1 is set).
func (s *scanner) digits(base int, invalid *int) (digsep int) {
	if base <= 10 {
		max := rune('0' + base)
		for isDecimal(s.source.ch) || s.source.ch == '_' {
			ds := 1
			if s.source.ch == '_' {
				ds = 2
			} else if s.source.ch >= max && *invalid < 0 {
				_, col := s.source.pos()
				*invalid = int(col - s.col) // record invalid rune index
			}
			digsep |= ds
			s.source.nextch()
		}
	} else {
		for isHex(s.source.ch) || s.source.ch == '_' {
			ds := 1
			if s.source.ch == '_' {
				ds = 2
			}
			digsep |= ds
			s.source.nextch()
		}
	}
	return
}

func (s *scanner) number(seenPoint bool) {
	ok := true
	kind := IntLit
	base := 10        // number base
	prefix := rune(0) // one of 0 (decimal), '0' (0-octal), 'x', 'o', or 'b'
	digsep := 0       // bit 0: digit present, bit 1: '_' present
	invalid := -1     // index of invalid digit in literal, or < 0

	// integer part
	if !seenPoint {
		if s.source.ch == '0' {
			s.source.nextch()
			switch lower(s.source.ch) {
			case 'x':
				s.source.nextch()
				base, prefix = 16, 'x'
			case 'o':
				s.source.nextch()
				base, prefix = 8, 'o'
			case 'b':
				s.source.nextch()
				base, prefix = 2, 'b'
			default:
				base, prefix = 8, '0'
				digsep = 1 // leading 0
			}
		}
		digsep |= s.digits(base, &invalid)
		if s.source.ch == '.' {
			if prefix == 'o' || prefix == 'b' {
				s.errorf("invalid radix point in %s literal", baseName(base))
				ok = false
			}
			s.source.nextch()
			seenPoint = true
		}
	}

	// fractional part
	if seenPoint {
		kind = FloatLit
		digsep |= s.digits(base, &invalid)
	}

	if digsep&1 == 0 && ok {
		s.errorf("%s literal has no digits", baseName(base))
		ok = false
	}

	// exponent
	if e := lower(s.source.ch); e == 'e' || e == 'p' {
		if ok {
			switch {
			case e == 'e' && prefix != 0 && prefix != '0':
				s.errorf("%q exponent requires decimal mantissa", s.source.ch)
				ok = false
			case e == 'p' && prefix != 'x':
				s.errorf("%q exponent requires hexadecimal mantissa", s.source.ch)
				ok = false
			}
		}
		s.source.nextch()
		kind = FloatLit
		if s.source.ch == '+' || s.source.ch == '-' {
			s.source.nextch()
		}
		digsep = s.digits(10, nil) | digsep&2 // don't lose sep bit
		if digsep&1 == 0 && ok {
			s.errorf("exponent has no digits")
			ok = false
		}
	} else if prefix == 'x' && kind == FloatLit && ok {
		s.errorf("hexadecimal mantissa requires a 'p' exponent")
		ok = false
	}

	// suffix 'i'
	if s.source.ch == 'i' {
		kind = ImagLit
		s.source.nextch()
	}

	s.setLit(kind, ok) // do this now so we can use s.lit below

	if kind == IntLit && invalid >= 0 && ok {
		s.errorAtf(invalid, "invalid digit %q in %s literal", s.lit[invalid], baseName(base))
		ok = false
	}

	if digsep&2 != 0 && ok {
		if i := invalidSep(s.lit); i >= 0 {
			s.errorAtf(i, "'_' must separate successive digits")
			ok = false
		}
	}

	s.bad = !ok // correct s.bad
}

func baseName(base int) string {
	switch base {
	case 2:
		return "binary"
	case 8:
		return "octal"
	case 10:
		return "decimal"
	case 16:
		return "hexadecimal"
	}
	panic("invalid base")
}

// invalidSep returns the index of the first invalid separator in x, or -1.
func invalidSep(x string) int {
	x1 := ' ' // prefix char, we only care if it's 'x'
	d := '.'  // digit, one of '_', '0' (a digit), or '.' (anything else)
	i := 0

	// a prefix counts as a digit
	if len(x) >= 2 && x[0] == '0' {
		x1 = lower(rune(x[1]))
		if x1 == 'x' || x1 == 'o' || x1 == 'b' {
			d = '0'
			i = 2
		}
	}

	// mantissa and exponent
	for ; i < len(x); i++ {
		p := d // previous digit
		d = rune(x[i])
		switch {
		case d == '_':
			if p != '0' {
				return i
			}
		case isDecimal(d) || x1 == 'x' && isHex(d):
			d = '0'
		default:
			if p == '_' {
				return i - 1
			}
			d = '.'
		}
	}
	if d == '_' {
		return len(x) - 1
	}

	return -1
}

func (s *scanner) rune() {
	ok := true
	s.source.nextch()

	n := 0
	for ; ; n++ {
		if s.source.ch == '\'' {
			if ok {
				if n == 0 {
					s.errorf("empty rune literal or unescaped '")
					ok = false
				} else if n != 1 {
					s.errorAtf(0, "more than one character in rune literal")
					ok = false
				}
			}
			s.source.nextch()
			break
		}
		if s.source.ch == '\\' {
			s.source.nextch()
			if !s.escape('\'') {
				ok = false
			}
			continue
		}
		if s.source.ch == '\n' {
			if ok {
				s.errorf("newline in rune literal")
				ok = false
			}
			break
		}
		if s.source.ch < 0 {
			if ok {
				s.errorAtf(0, "rune literal not terminated")
				ok = false
			}
			break
		}
		s.source.nextch()
	}

	s.setLit(RuneLit, ok)
}

func (s *scanner) stdString() {
	ok := true
	s.source.nextch()

	for {
		if s.source.ch == '"' {
			s.source.nextch()
			break
		}
		if s.source.ch == '\\' {
			s.source.nextch()
			if !s.escape('"') {
				ok = false
			}
			continue
		}
		if s.source.ch == '\n' {
			s.errorf("newline in string")
			ok = false
			break
		}
		if s.source.ch < 0 {
			s.errorAtf(0, "string not terminated")
			ok = false
			break
		}
		s.source.nextch()
	}

	s.setLit(StringLit, ok)
}

func (s *scanner) rawString() {
	ok := true
	s.source.nextch()

	for {
		if s.source.ch == '`' {
			s.source.nextch()
			break
		}
		if s.source.ch < 0 {
			s.errorAtf(0, "string not terminated")
			ok = false
			break
		}
		s.source.nextch()
	}
	// We leave CRs in the string since they are part of the
	// literal (even though they are not part of the literal
	// value).

	s.setLit(StringLit, ok)
}

func (s *scanner) comment(text string) {
	s.errorAtf(0, "%s", text)
}

func (s *scanner) skipLine() {
	// don't consume '\n' - needed for nlsemi logic
	for s.source.ch >= 0 && s.source.ch != '\n' {
		s.source.nextch()
	}
}

func (s *scanner) lineComment() {
	// opening has already been consumed

	if s.mode&comments != 0 {
		s.skipLine()
		s.comment(s.source.segment())
		return
	}

	// are we saving directives? or is this definitely not a directive?
	if s.mode&directives == 0 || (s.source.ch != 'g' && s.source.ch != 'l') {
		s.source.stop()
		s.skipLine()
		return
	}

	// recognize go: or line directives
	prefix := "go:"
	if s.source.ch == 'l' {
		prefix = "line "
	}
	for _, m := range prefix {
		if s.source.ch != m {
			s.source.stop()
			s.skipLine()
			return
		}
		s.source.nextch()
	}

	// directive text
	s.skipLine()
	s.comment(s.source.segment())
}

func (s *scanner) skipComment() bool {
	for s.source.ch >= 0 {
		for s.source.ch == '*' {
			s.source.nextch()
			if s.source.ch == '/' {
				s.source.nextch()
				return true
			}
		}
		s.source.nextch()
	}
	s.errorAtf(0, "comment not terminated")
	return false
}

func (s *scanner) fullComment() {
	/* opening has already been consumed */

	if s.mode&comments != 0 {
		if s.skipComment() {
			s.comment(s.source.segment())
		}
		return
	}

	if s.mode&directives == 0 || s.source.ch != 'l' {
		s.source.stop()
		s.skipComment()
		return
	}

	// recognize line directive
	const prefix = "line "
	for _, m := range prefix {
		if s.source.ch != m {
			s.source.stop()
			s.skipComment()
			return
		}
		s.source.nextch()
	}

	// directive text
	if s.skipComment() {
		s.comment(s.source.segment())
	}
}

func (s *scanner) escape(quote rune) bool {
	var n int
	var base, max uint32

	switch s.source.ch {
	case quote, 'a', 'b', 'f', 'n', 'r', 't', 'v', '\\':
		s.source.nextch()
		return true
	case '0', '1', '2', '3', '4', '5', '6', '7':
		n, base, max = 3, 8, 255
	case 'x':
		s.source.nextch()
		n, base, max = 2, 16, 255
	case 'u':
		s.source.nextch()
		n, base, max = 4, 16, unicode.MaxRune
	case 'U':
		s.source.nextch()
		n, base, max = 8, 16, unicode.MaxRune
	default:
		if s.source.ch < 0 {
			return true // complain in caller about EOF
		}
		s.errorf("unknown escape")
		return false
	}

	var x uint32
	for i := n; i > 0; i-- {
		if s.source.ch < 0 {
			return true // complain in caller about EOF
		}
		d := base
		if isDecimal(s.source.ch) {
			d = uint32(s.source.ch) - '0'
		} else if 'a' <= lower(s.source.ch) && lower(s.source.ch) <= 'f' {
			d = uint32(lower(s.source.ch)) - 'a' + 10
		}
		if d >= base {
			s.errorf("invalid character %q in %s escape", s.source.ch, baseName(int(base)))
			return false
		}
		// d < base
		x = x*base + d
		s.source.nextch()
	}

	if x > max && base == 8 {
		s.errorf("octal escape value %d > 255", x)
		return false
	}

	if x > max || 0xD800 <= x && x < 0xE000 /* surrogate range */ {
		s.errorf("escape is invalid Unicode code point %#U", x)
		return false
	}

	return true
}
