// Copyright 2016 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package syntax

import (
	"fmt"
	"io"
	"strings"
)

const debug = false
const trace = false

type parser struct {
	mode Mode
	tapescanner

	fnest  int    // function nesting level (for error handling)
	xnest  int    // expression nesting level (for complit ambiguity resolution)
	indent []byte // tracing support

	asyncCalls []asyncCall
}

type asyncCall struct {
	fn   func() // parser function
	open int    // index of open punctuation token

	// saved parser state
	base   *PosBase
	fnest  int
	xnest  int
	indent []byte
}

func (p *parser) capture(fn func()) asyncCall {
	if p.pragh != nil && p.pragh.Take() != nil {
		panic("current Pragma before async call")
	}

	return asyncCall{
		fn:     fn,
		open:   p.tapepos,
		base:   p.base,
		fnest:  p.fnest,
		xnest:  p.xnest,
		indent: p.indent,
	}
}

func (call asyncCall) do(p *parser) {
	p.tapepos = call.open
	p.tapeelem = p.tape[call.open]

	p.base = call.base
	p.fnest = call.fnest
	p.xnest = call.xnest
	p.indent = call.indent

	call.fn()

	if p.pragh != nil && p.pragh.Take() != nil {
		panic("current Pragma after async call")
	}

	p.checkLinks(call.open)
}

func (p *parser) init(file *PosBase, src string, errh ErrorHandler, pragh PragmaHandler, mode Mode) {
	p.file = file
	p.errh = errh
	p.mode = mode
	p.pragh = pragh
	p.tapescanner.init(src, directives)

	p.base = file
	p.first = nil
	p.errcnt = 0

	p.fnest = 0
	p.xnest = 0
	p.indent = nil

	p.next()
}

func (p *parser) fini() error {
	for i := 0; i < len(p.asyncCalls); i++ {
		p.asyncCalls[i].do(p)
	}
	return p.first
}

// Deprecated: Use init instead.
func (p *parser) initReader(file *PosBase, r io.Reader, errh ErrorHandler, pragh PragmaHandler, mode Mode) {
	p.init(file, readAllString(r), errh, pragh, mode)
}

func (p *parser) allowGenerics() bool { return p.mode&AllowGenerics != 0 }

// takePragma returns the current parsed pragmas
// and clears them from the parser state.
func (p *parser) takePragma() Pragma {
	if p.pragh != nil {
		return p.pragh.Take()
	}
	return nil
}

// clearPragma is called at the end of a statement or
// other Go form that does NOT accept a pragma.
// It sends the pragma back to the pragma handler
// to be reported as unused.
func (p *parser) clearPragma() {
	if p.pragh != nil {
		p.pragh.Reset()
	}
}

func (p *parser) got(tok token) bool {
	if p.tok == tok {
		p.next()
		return true
	}
	return false
}

func (p *parser) want(tok token) {
	if !p.got(tok) {
		p.syntaxError("expecting " + tokstring(tok))
		p.advance()
	}
}

// gotAssign is like got(_Assign) but it also accepts ":="
// (and reports an error) for better parser error recovery.
func (p *parser) gotAssign() bool {
	switch p.tok {
	case _Define:
		p.syntaxError("expecting =")
		fallthrough
	case _Assign:
		p.next()
		return true
	}
	return false
}

// ----------------------------------------------------------------------------
// Error handling

// syntaxErrorAt reports a syntax error at the given position.
func (p *parser) syntaxErrorAt(pos Pos, msg string) {
	if trace {
		p.print("syntax error: " + msg)
	}

	if p.tok == _EOF && p.first != nil {
		return // avoid meaningless follow-up errors
	}

	// add punctuation etc. as needed to msg
	switch {
	case msg == "":
		// nothing to do
	case strings.HasPrefix(msg, "in "), strings.HasPrefix(msg, "at "), strings.HasPrefix(msg, "after "):
		msg = " " + msg
	case strings.HasPrefix(msg, "expecting "):
		msg = ", " + msg
	default:
		// plain error - we don't care about current token
		p.errorAt(pos, "syntax error: "+msg)
		return
	}

	// determine token string
	var tok string
	switch p.tok {
	case _Name, _Semi:
		tok = p.lit
	case _Literal:
		tok = "literal " + p.lit
	case _Operator:
		tok = p.op.String()
	case _AssignOp:
		tok = p.op.String() + "="
	case _IncOp:
		tok = p.op.String()
		tok += tok
	default:
		tok = tokstring(p.tok)
	}

	p.errorAt(pos, "syntax error: unexpected "+tok+msg)
}

// tokstring returns the English word for selected punctuation tokens
// for more readable error messages. Use tokstring (not tok.String())
// for user-facing (error) messages; use tok.String() for debugging
// output.
func tokstring(tok token) string {
	switch tok {
	case _Comma:
		return "comma"
	case _Semi:
		return "semicolon or newline"
	}
	return tok.String()
}

// Convenience methods using the current token position.
func (p *parser) pos() Pos               { return p.posAt(p.line, p.col) }
func (p *parser) error(msg string)       { p.errorAt(p.pos(), msg) }
func (p *parser) syntaxError(msg string) { p.syntaxErrorAt(p.pos(), msg) }

// The stopset contains keywords that start a statement.
// They are good synchronization points in case of syntax
// errors and (usually) shouldn't be skipped over.
const stopset uint64 = 1<<_Break |
	1<<_Const |
	1<<_Continue |
	1<<_Defer |
	1<<_Fallthrough |
	1<<_For |
	1<<_Go |
	1<<_Goto |
	1<<_If |
	1<<_Return |
	1<<_Select |
	1<<_Switch |
	1<<_Type |
	1<<_Var

// Advance consumes tokens until it finds a token of the stopset or followlist.
// The stopset is only considered if we are inside a function (p.fnest > 0).
// The followlist is the list of valid tokens that can follow a production;
// if it is empty, exactly one (non-EOF) token is consumed to ensure progress.
func (p *parser) advance(followlist ...token) {
	if trace {
		p.print(fmt.Sprintf("advance %s", followlist))
	}

	// compute follow set
	// (not speed critical, advance is only called in error situations)
	var followset uint64 = 1 << _EOF // don't skip over EOF
	if len(followlist) > 0 {
		if p.fnest > 0 {
			followset |= stopset
		}
		for _, tok := range followlist {
			followset |= 1 << tok
		}
	}

	for !contains(followset, p.tok) {
		if trace {
			p.print("skip " + p.tok.String())
		}
		p.next()
		if len(followlist) == 0 {
			break
		}
	}

	if trace {
		p.print("next " + p.tok.String())
	}
}

// usage: defer p.trace(msg)()
func (p *parser) trace(msg string) func() {
	p.print(msg + " (")
	const tab = ". "
	p.indent = append(p.indent, tab...)
	return func() {
		p.indent = p.indent[:len(p.indent)-len(tab)]
		if x := recover(); x != nil {
			panic(x) // skip print_trace
		}
		p.print(")")
	}
}

func (p *parser) print(msg string) {
	fmt.Printf("%5d: %s%s\n", p.line, p.indent, msg)
}

// ----------------------------------------------------------------------------
// Package files
//
// Parse methods are annotated with matching Go productions as appropriate.
// The annotations are intended as guidelines only since a single Go grammar
// rule may be covered by multiple parse methods and vice versa.
//
// Excluding methods returning slices, parse methods named xOrNil may return
// nil; all others are expected to return a valid non-nil node.

// SourceFile = PackageClause ";" { ImportDecl ";" } { TopLevelDecl ";" } .
func (p *parser) fileOrNil() *File {
	if trace {
		defer p.trace("file")()
	}

	f := new(File)
	f.pos = p.pos()

	// PackageClause
	if !p.got(_Package) {
		p.syntaxError("package statement must be first")
		return nil
	}
	f.Pragma = p.takePragma()
	f.PkgName = p.name()
	p.want(_Semi)

	// don't bother continuing if package clause has errors
	if p.first != nil {
		return nil
	}

	// { ImportDecl ";" }
	for p.tok == _Import {
		f.DeclList = append(f.DeclList, p.genDecl())
		p.want(_Semi)
	}

	// { TopLevelDecl ";" }
	for p.tok != _EOF {
		switch p.tok {
		case _Const, _Type, _Var:
			f.DeclList = append(f.DeclList, p.genDecl())

		case _Func:
			p.next()
			if d := p.funcDeclOrNil(); d != nil {
				f.DeclList = append(f.DeclList, d)
			}

		default:
			if p.tok == _Lbrace && len(f.DeclList) > 0 && isEmptyFuncDecl(f.DeclList[len(f.DeclList)-1]) {
				// opening { of function declaration on next line
				p.syntaxError("unexpected semicolon or newline before {")
			} else {
				p.syntaxError("non-declaration statement outside function body")
			}
			p.advance(_Const, _Type, _Var, _Func)
			continue
		}

		// Reset p.pragma BEFORE advancing to the next token (consuming ';')
		// since comments before may set pragmas for the next function decl.
		p.clearPragma()

		if p.tok != _EOF && !p.got(_Semi) {
			p.syntaxError("after top level declaration")
			p.advance(_Const, _Type, _Var, _Func)
		}
	}
	// p.tok == _EOF

	p.clearPragma()
	f.EOF = p.pos()

	return f
}

func isEmptyFuncDecl(dcl Decl) bool {
	f, ok := dcl.(*FuncDecl)
	return ok && f.Body == nil
}

// ----------------------------------------------------------------------------
// Declarations

// list parses a possibly empty, sep-separated list of elements, optionally
// followed by sep, and closed by close (or EOF). sep must be one of _Comma
// or _Semi, and close must be one of _Rparen, _Rbrace, or _Rbrack.
//
// For each list element, f is called. Specifically, unless we're at close
// (or EOF), f is called at least once. After f returns true, no more list
// elements are accepted. list returns the position of the closing token.
//
// list = [ f { sep f } [sep] ] close .
//
func (p *parser) list(sep, close token, f func() bool) Pos {
	if debug && (sep != _Comma && sep != _Semi || close != _Rparen && close != _Rbrace && close != _Rbrack) {
		panic("invalid sep or close argument for list")
	}

	done := false
	for p.tok != _EOF && p.tok != close && !done {
		done = f()
		// sep is optional before close
		if !p.got(sep) && p.tok != close {
			p.syntaxError(fmt.Sprintf("expecting %s or %s", tokstring(sep), tokstring(close)))
			p.advance(_Rparen, _Rbrack, _Rbrace)
			if p.tok != close {
				// position could be better but we had an error so we don't care
				return p.pos()
			}
		}
	}

	pos := p.pos()
	p.want(close)
	return pos
}

// appendGroup(f) = f | "(" { f ";" } ")" . // ";" is optional before ")"
func (p *parser) genDecl() *GenDecl {
	s := new(GenDecl)
	s.pos = p.pos()
	s.Tok = p.tok
	p.next()

	var spec func(*parser) Spec
	switch s.Tok {
	case _Import:
		spec = (*parser).importSpec
	case _Const:
		spec = (*parser).constSpec
	case _Type:
		spec = (*parser).typeSpec
	case _Var:
		spec = (*parser).varSpec
	}

	if p.tok == _Lparen {
		// must clearPragma before consuming "("!
		// TODO(mdempsky): Elaborate.
		p.clearPragma()

		s.Lparen, s.Rparen = p.asyncList(_Lparen, _Semi, _Rparen, func() bool {
			if x := spec(p); x != nil {
				s.SpecList = append(s.SpecList, x)
			}
			return false
		})
	} else {
		if x := spec(p); x != nil {
			s.SpecList = append(s.SpecList, x)
		}
	}
	return s
}

// ImportSpec = [ "." | PackageName ] ImportPath .
// ImportPath = string_lit .
func (p *parser) importSpec() Spec {
	if trace {
		defer p.trace("importDecl")()
	}

	d := new(ImportSpec)
	d.pos = p.pos()
	d.Pragma = p.takePragma()

	switch p.tok {
	case _Name:
		d.LocalPkgName = p.name()
	case _Dot:
		d.LocalPkgName = NewName(p.pos(), ".")
		p.next()
	}
	d.Path = p.oliteral()
	if d.Path == nil {
		p.syntaxError("missing import path")
		p.advance(_Semi, _Rparen)
		return d
	}
	if !d.Path.Bad && d.Path.Kind != StringLit {
		p.syntaxError("import path must be a string")
		d.Path.Bad = true
	}
	// d.Path.Bad || d.Path.Kind == StringLit

	return d
}

// ConstSpec = IdentifierList [ [ Type ] "=" ExpressionList ] .
func (p *parser) constSpec() Spec {
	if trace {
		defer p.trace("constDecl")()
	}

	d := new(ConstSpec)
	d.pos = p.pos()
	d.Pragma = p.takePragma()

	d.NameList = p.nameList(p.name())
	if p.tok != _EOF && p.tok != _Semi && p.tok != _Rparen {
		d.Type = p.typeOrNil()
		if p.gotAssign() {
			d.Values = p.exprList()
		}
	}

	return d
}

// TypeSpec = identifier [ TypeParams ] [ "=" ] Type .
func (p *parser) typeSpec() Spec {
	if trace {
		defer p.trace("typeDecl")()
	}

	d := new(TypeSpec)
	d.pos = p.pos()
	d.Pragma = p.takePragma()

	d.Name = p.name()
	if p.allowGenerics() && p.tok == _Lbrack {
		// d.Name "[" ...
		// array/slice type or type parameter list
		pos := p.pos()
		open := p.tapepos
		p.next()
		switch p.tok {
		case _Name:
			// We may have an array type or a type parameter list.
			// In either case we expect an expression x (which may
			// just be a name, or a more complex expression) which
			// we can analyze further.
			//
			// A type parameter list may have a type bound starting
			// with a "[" as in: P []E. In that case, simply parsing
			// an expression would lead to an error: P[] is invalid.
			// But since index or slice expressions are never constant
			// and thus invalid array length expressions, if we see a
			// "[" following a name it must be the start of an array
			// or slice constraint. Only if we don't see a "[" do we
			// need to parse a full expression.
			var x Expr = p.name()
			if p.tok != _Lbrack {
				// To parse the expression starting with name, expand
				// the call sequence we would get by passing in name
				// to parser.expr, and pass in name to parser.pexpr.
				p.xnest++
				x = p.binaryExpr(p.pexpr(x, false), 0)
				p.xnest--
			}

			// analyze the cases
			var pname *Name // pname != nil means pname is the type parameter name
			var ptype Expr  // ptype != nil means ptype is the type parameter type; pname != nil in this case
			switch t := x.(type) {
			case *Name:
				// Unless we see a "]", we are at the start of a type parameter list.
				if p.tok != _Rbrack {
					// d.Name "[" name ...
					pname = t
					// no ptype
				}
			case *Operation:
				// If we have an expression of the form name*T, and T is a (possibly
				// parenthesized) type literal or the next token is a comma, we are
				// at the start of a type parameter list.
				if name, _ := t.X.(*Name); name != nil {
					if t.Op == Mul && (isTypeLit(t.Y) || p.tok == _Comma) {
						// d.Name "[" name "*" t.Y
						// d.Name "[" name "*" t.Y ","
						t.X, t.Y = t.Y, nil // convert t into unary *t.Y
						pname = name
						ptype = t
					}
				}
			case *CallExpr:
				// If we have an expression of the form name(T), and T is a (possibly
				// parenthesized) type literal or the next token is a comma, we are
				// at the start of a type parameter list.
				if name, _ := t.Fun.(*Name); name != nil {
					if len(t.ArgList) == 1 && !t.HasDots && (isTypeLit(t.ArgList[0]) || p.tok == _Comma) {
						// d.Name "[" name "(" t.ArgList[0] ")"
						// d.Name "[" name "(" t.ArgList[0] ")" ","
						pname = name
						ptype = t.ArgList[0]
					}
				}
			}

			if pname != nil {
				// d.Name "[" pname ...
				// d.Name "[" pname ptype ...
				// d.Name "[" pname ptype "," ...
				d.TParamList = p.paramList(pname, ptype, _Rbrack, true)
				p.checkLinks(open)
				d.Alias = p.gotAssign()
				d.Type = p.typeOrNil()
			} else {
				// d.Name "[" x ...
				d.Type = p.arrayType(open, pos, x)
			}
		case _Rbrack:
			// d.Name "[" "]" ...
			p.next()
			p.checkLinks(open)
			d.Type = p.sliceType(pos)
		default:
			// d.Name "[" ...
			d.Type = p.arrayType(open, pos, nil)
		}
	} else {
		d.Alias = p.gotAssign()
		d.Type = p.typeOrNil()
	}

	if d.Type == nil {
		d.Type = p.badExpr()
		p.syntaxError("in type declaration")
		p.advance(_Semi, _Rparen)
	}

	return d
}

// isTypeLit reports whether x is a (possibly parenthesized) type literal.
func isTypeLit(x Expr) bool {
	switch x := x.(type) {
	case *ArrayType, *StructType, *FuncType, *InterfaceType, *SliceType, *MapType, *ChanType:
		return true
	case *Operation:
		// *T may be a pointer dereferenciation.
		// Only consider *T as type literal if T is a type literal.
		return x.Op == Mul && x.Y == nil && isTypeLit(x.X)
	case *ParenExpr:
		return isTypeLit(x.X)
	}
	return false
}

// VarSpec = IdentifierList ( Type [ "=" ExpressionList ] | "=" ExpressionList ) .
func (p *parser) varSpec() Spec {
	if trace {
		defer p.trace("varDecl")()
	}

	d := new(VarSpec)
	d.pos = p.pos()
	d.Pragma = p.takePragma()

	d.NameList = p.nameList(p.name())
	if p.gotAssign() {
		d.Values = p.exprList()
	} else {
		d.Type = p.type_()
		if p.gotAssign() {
			d.Values = p.exprList()
		}
	}

	return d
}

// FunctionDecl = "func" FunctionName [ TypeParams ] ( Function | Signature ) .
// FunctionName = identifier .
// Function     = Signature FunctionBody .
// MethodDecl   = "func" Receiver MethodName ( Function | Signature ) .
// Receiver     = Parameters .
func (p *parser) funcDeclOrNil() *FuncDecl {
	if trace {
		defer p.trace("funcDecl")()
	}

	f := new(FuncDecl)
	f.pos = p.pos()
	f.Pragma = p.takePragma()

	if p.tok == _Lparen {
		p.async(func() {
			p.next()
			rcvr := p.paramList(nil, nil, _Rparen, false)
			switch len(rcvr) {
			case 0:
				p.error("method has no receiver")
			default:
				p.error("method has multiple receivers")
				fallthrough
			case 1:
				f.Recv = rcvr[0]
			}
		})
	}

	if p.tok != _Name {
		p.syntaxError("expecting name or (")
		p.advance(_Lbrace, _Semi)
		return nil
	}

	f.Name = p.name()

	context := ""
	if f.Recv != nil && p.mode&AllowMethodTypeParams == 0 {
		context = "method" // don't permit (method) type parameters in funcType
	}
	f.Type = p.funcType(context, &f.TParamList)

	if p.tok == _Lbrace {
		f.Body = p.funcBody()
	}

	return f
}

func (p *parser) funcBody() *BlockStmt {
	p.fnest++
	errcnt := p.errcnt
	body := p.blockStmt("")
	p.fnest--

	// Don't check branches if there were syntax errors in the function
	// as it may lead to spurious errors (e.g., see test/switch2.go) or
	// possibly crashes due to incomplete syntax trees.
	if p.mode&CheckBranches != 0 && errcnt == p.errcnt {
		checkBranches(body, p.errh)
	}

	return body
}

// ----------------------------------------------------------------------------
// Expressions

func (p *parser) expr() Expr {
	if trace {
		defer p.trace("expr")()
	}

	return p.binaryExpr(nil, 0)
}

// Expression = UnaryExpr | Expression binary_op Expression .
func (p *parser) binaryExpr(x Expr, prec int) Expr {
	// don't trace binaryExpr - only leads to overly nested trace output

	if x == nil {
		x = p.unaryExpr()
	}
	for p.tok == _Operator || p.tok == _Star {
		tprec := p.op.prec()
		if tprec <= prec {
			break
		}

		t := new(Operation)
		t.pos = p.pos()
		t.Op = p.op
		p.next()
		t.X = x
		t.Y = p.binaryExpr(nil, tprec)
		x = t
	}
	return x
}

// UnaryExpr = PrimaryExpr | unary_op UnaryExpr .
func (p *parser) unaryExpr() Expr {
	if trace {
		defer p.trace("unaryExpr")()
	}

	switch p.tok {
	case _Operator, _Star:
		switch p.op {
		case Mul, Add, Sub, Not, Xor:
			x := new(Operation)
			x.pos = p.pos()
			x.Op = p.op
			p.next()
			x.X = p.unaryExpr()
			return x

		case And:
			x := new(Operation)
			x.pos = p.pos()
			x.Op = And
			p.next()
			// unaryExpr may have returned a parenthesized composite literal
			// (see comment in operand) - remove parentheses if any
			x.X = Unparen(p.unaryExpr())
			return x
		}

	case _Arrow:
		// receive op (<-x) or receive-only channel (<-chan E)
		pos := p.pos()
		p.next()

		// If the next token is _Chan we still don't know if it is
		// a channel (<-chan int) or a receive op (<-chan int(ch)).
		// We only know once we have found the end of the unaryExpr.

		x := p.unaryExpr()

		// There are two cases:
		//
		//   <-chan...  => <-x is a channel type
		//   <-x        => <-x is a receive operation
		//
		// In the first case, <- must be re-associated with
		// the channel type parsed already:
		//
		//   <-(chan E)   =>  (<-chan E)
		//   <-(chan<-E)  =>  (<-chan (<-E))

		if _, ok := x.(*ChanType); ok {
			// x is a channel type => re-associate <-
			dir := SendOnly
			t := x
			for dir == SendOnly {
				c, ok := t.(*ChanType)
				if !ok {
					break
				}
				dir = c.Dir
				if dir == RecvOnly {
					// t is type <-chan E but <-<-chan E is not permitted
					// (report same error as for "type _ <-<-chan E")
					p.syntaxError("unexpected <-, expecting chan")
					// already progressed, no need to advance
				}
				c.Dir = RecvOnly
				t = c.Elem
			}
			if dir == SendOnly {
				// channel dir is <- but channel element E is not a channel
				// (report same error as for "type _ <-chan<-E")
				p.syntaxError(fmt.Sprintf("unexpected %s, expecting chan", NodeString(t)))
				// already progressed, no need to advance
			}
			return x
		}

		// x is not a channel type => we have a receive op
		o := new(Operation)
		o.pos = pos
		o.Op = Recv
		o.X = x
		return o
	}

	// TODO(mdempsky): We need parens here so we can report an
	// error for "(x) := true". It should be possible to detect
	// and reject that more efficiently though.
	return p.pexpr(nil, true)
}

// callStmt parses call-like statements that can be preceded by 'defer' and 'go'.
func (p *parser) callStmt() *CallStmt {
	if trace {
		defer p.trace("callStmt")()
	}

	s := new(CallStmt)
	s.pos = p.pos()
	s.Tok = p.tok // _Defer or _Go
	p.next()

	x := p.pexpr(nil, p.tok == _Lparen) // keep_parens so we can report error below
	if t := Unparen(x); t != x {
		p.errorAt(x.Pos(), fmt.Sprintf("expression in %s must not be parenthesized", s.Tok))
		// already progressed, no need to advance
		x = t
	}

	cx, ok := x.(*CallExpr)
	if !ok {
		p.errorAt(x.Pos(), fmt.Sprintf("expression in %s must be function call", s.Tok))
		// already progressed, no need to advance
		cx = new(CallExpr)
		cx.pos = x.Pos()
		cx.Fun = x // assume common error of missing parentheses (function invocation)
	}

	s.Call = cx
	return s
}

// Operand     = Literal | OperandName | MethodExpr | "(" Expression ")" .
// Literal     = BasicLit | CompositeLit | FunctionLit .
// BasicLit    = int_lit | float_lit | imaginary_lit | rune_lit | string_lit .
// OperandName = identifier | QualifiedIdent.
func (p *parser) operand(keep_parens bool) Expr {
	if trace {
		defer p.trace("operand " + p.tok.String())()
	}

	switch p.tok {
	case _Name:
		return p.name()

	case _Literal:
		return p.oliteral()

	case _Lparen:
		pos := p.pos()
		p.next()
		p.xnest++
		x := p.expr()
		p.xnest--
		p.want(_Rparen)

		// Optimization: Record presence of ()'s only where needed
		// for error reporting. Don't bother in other cases; it is
		// just a waste of memory and time.
		//
		// Parentheses are not permitted around T in a composite
		// literal T{}. If the next token is a {, assume x is a
		// composite literal type T (it may not be, { could be
		// the opening brace of a block, but we don't know yet).
		if p.tok == _Lbrace {
			keep_parens = true
		}

		// Parentheses are also not permitted around the expression
		// in a go/defer statement. In that case, operand is called
		// with keep_parens set.
		if keep_parens {
			px := new(ParenExpr)
			px.pos = pos
			px.X = x
			x = px
		}
		return x

	case _Func:
		pos := p.pos()
		p.next()
		ftyp := p.funcType("function literal", nil)
		if p.tok == _Lbrace {
			p.xnest++

			f := new(FuncLit)
			f.pos = pos
			f.Type = ftyp
			f.Body = p.funcBody()

			p.xnest--
			return f
		}
		return ftyp

	case _Lbrack, _Chan, _Map, _Struct, _Interface:
		return p.type_() // othertype

	default:
		x := p.badExpr()
		p.syntaxError("expecting expression")
		p.advance(_Rparen, _Rbrack, _Rbrace)
		return x
	}

	// Syntactically, composite literals are operands. Because a complit
	// type may be a qualified identifier which is handled by pexpr
	// (together with selector expressions), complits are parsed there
	// as well (operand is only called from pexpr).
}

// PrimaryExpr =
// 	Operand |
// 	Conversion |
// 	PrimaryExpr Selector |
// 	PrimaryExpr Index |
// 	PrimaryExpr Slice |
// 	PrimaryExpr TypeAssertion |
// 	PrimaryExpr Arguments .
//
// Selector       = "." identifier .
// Index          = "[" Expression "]" .
// Slice          = "[" ( [ Expression ] ":" [ Expression ] ) |
//                      ( [ Expression ] ":" Expression ":" Expression )
//                  "]" .
// TypeAssertion  = "." "(" Type ")" .
// Arguments      = "(" [ ( ExpressionList | Type [ "," ExpressionList ] ) [ "..." ] [ "," ] ] ")" .
func (p *parser) pexpr(x Expr, keep_parens bool) Expr {
	if trace {
		defer p.trace("pexpr")()
	}

	if x == nil {
		x = p.operand(keep_parens)
	}

loop:
	for {
		pos := p.pos()
		switch p.tok {
		case _Dot:
			p.next()
			switch p.tok {
			case _Name:
				// pexpr '.' sym
				t := new(SelectorExpr)
				t.pos = pos
				t.X = x
				t.Sel = p.name()
				x = t

			case _Lparen:
				p.next()
				if p.got(_Type) {
					t := new(TypeSwitchGuard)
					// t.Lhs is filled in by parser.simpleStmt
					t.pos = pos
					t.X = x
					x = t
				} else {
					t := new(AssertExpr)
					t.pos = pos
					t.X = x
					t.Type = p.type_()
					x = t
				}
				p.want(_Rparen)

			default:
				p.syntaxError("expecting name or (")
				p.advance(_Semi, _Rparen)
			}

		case _Lbrack:
			p.next()

			if p.tok == _Rbrack {
				// invalid empty instance, slice or index expression; accept but complain
				p.syntaxError("expecting operand")
				p.next()
				break
			}

			var i Expr
			if p.tok != _Colon {
				if p.mode&AllowGenerics == 0 {
					p.xnest++
					i = p.expr()
					p.xnest--
					if p.got(_Rbrack) {
						// x[i]
						t := new(IndexExpr)
						t.pos = pos
						t.X = x
						t.Index = i
						x = t
						break
					}
				} else {
					var comma bool
					i, comma = p.typeList()
					if comma || p.tok == _Rbrack {
						p.want(_Rbrack)
						// x[i,] or x[i, j, ...]
						t := new(IndexExpr)
						t.pos = pos
						t.X = x
						t.Index = i
						x = t
						break
					}
				}
			}

			// x[i:...
			// For better error message, don't simply use p.want(_Colon) here (issue #47704).
			if !p.got(_Colon) {
				if p.mode&AllowGenerics == 0 {
					p.syntaxError("expecting : or ]")
					p.advance(_Colon, _Rbrack)
				} else {
					p.syntaxError("expecting comma, : or ]")
					p.advance(_Comma, _Colon, _Rbrack)
				}
			}
			p.xnest++
			t := new(SliceExpr)
			t.pos = pos
			t.X = x
			t.Index[0] = i
			if p.tok != _Colon && p.tok != _Rbrack {
				// x[i:j...
				t.Index[1] = p.expr()
			}
			if p.tok == _Colon {
				t.Full = true
				// x[i:j:...]
				if t.Index[1] == nil {
					p.error("middle index required in 3-index slice")
					t.Index[1] = p.badExpr()
				}
				p.next()
				if p.tok != _Rbrack {
					// x[i:j:k...
					t.Index[2] = p.expr()
				} else {
					p.error("final index required in 3-index slice")
					t.Index[2] = p.badExpr()
				}
			}
			p.xnest--
			p.want(_Rbrack)
			x = t

		case _Lparen:
			t := new(CallExpr)
			t.pos = pos
			t.Fun = x

			// TODO(mdempsky): This can't be async yet, because
			// parser.typeDecl introspects the AST from parsing `type
			// T[F(X)` to recognize that "F(X)" (the CallExpr constructed
			// here) could actually be "F (X)" (i.e., a type parameter F of
			// parenthesized type X).
			p.xnest++
			p.asyncTODO(func() {
				p.next()
				p.list(_Comma, _Rparen, func() bool {
					t.ArgList = append(t.ArgList, p.expr())
					if p.got(_DotDotDot) {
						t.HasDots = true
						return true
					}
					return false
				})
			})
			p.xnest--
			x = t

		case _Lbrace:
			// operand may have returned a parenthesized complit
			// type; accept it but complain if we have a complit
			t := Unparen(x)
			// determine if '{' belongs to a composite literal or a block statement
			complit_ok := false
			switch t.(type) {
			case *Name, *SelectorExpr:
				if p.xnest >= 0 {
					// x is possibly a composite literal type
					complit_ok = true
				}
			case *IndexExpr:
				if p.xnest >= 0 && !isValue(t) {
					// x is possibly a composite literal type
					complit_ok = true
				}
			case *ArrayType, *SliceType, *StructType, *MapType:
				// x is a comptype
				complit_ok = true
			}
			if !complit_ok {
				break loop
			}
			if t != x {
				p.syntaxError("cannot parenthesize type in composite literal")
				// already progressed, no need to advance
			}
			n := p.complitexpr()
			n.Type = x
			x = n

		default:
			break loop
		}
	}

	return x
}

// isValue reports whether x syntactically must be a value (and not a type) expression.
func isValue(x Expr) bool {
	switch x := x.(type) {
	case *BasicLit, *CompositeLit, *FuncLit, *SliceExpr, *AssertExpr, *TypeSwitchGuard, *CallExpr:
		return true
	case *Operation:
		return x.Op != Mul || x.Y != nil // *T may be a type
	case *ParenExpr:
		return isValue(x.X)
	case *IndexExpr:
		return isValue(x.X) || isValue(x.Index)
	}
	return false
}

// Element = Expression | LiteralValue .
func (p *parser) bare_complitexpr() Expr {
	if trace {
		defer p.trace("bare_complitexpr")()
	}

	if p.tok == _Lbrace {
		// '{' start_complit braced_keyval_list '}'
		return p.complitexpr()
	}

	return p.expr()
}

// LiteralValue = "{" [ ElementList [ "," ] ] "}" .
func (p *parser) complitexpr() *CompositeLit {
	if trace {
		defer p.trace("complitexpr")()
	}

	p.xnest++
	x := new(CompositeLit)
	x.pos, x.Rbrace = p.asyncList(_Lbrace, _Comma, _Rbrace, func() bool {
		// value
		e := p.bare_complitexpr()
		if p.tok == _Colon {
			// key ':' value
			l := new(KeyValueExpr)
			l.pos = p.pos()
			p.next()
			l.Key = e
			l.Value = p.bare_complitexpr()
			e = l
			x.NKeys++
		}
		x.ElemList = append(x.ElemList, e)
		return false
	})
	p.xnest--

	return x
}

// ----------------------------------------------------------------------------
// Types

func (p *parser) type_() Expr {
	if trace {
		defer p.trace("type_")()
	}

	typ := p.typeOrNil()
	if typ == nil {
		typ = p.badExpr()
		p.syntaxError("expecting type")
		p.advance(_Comma, _Colon, _Semi, _Rparen, _Rbrack, _Rbrace)
	}

	return typ
}

func newIndirect(pos Pos, typ Expr) Expr {
	o := new(Operation)
	o.pos = pos
	o.Op = Mul
	o.X = typ
	return o
}

// typeOrNil is like type_ but it returns nil if there was no type
// instead of reporting an error.
//
// Type     = TypeName | TypeLit | "(" Type ")" .
// TypeName = identifier | QualifiedIdent .
// TypeLit  = ArrayType | StructType | PointerType | FunctionType | InterfaceType |
// 	      SliceType | MapType | Channel_Type .
func (p *parser) typeOrNil() Expr {
	if trace {
		defer p.trace("typeOrNil")()
	}

	pos := p.pos()
	switch p.tok {
	case _Star:
		// ptrtype
		p.next()
		return newIndirect(pos, p.type_())

	case _Arrow:
		// recvchantype
		p.next()
		p.want(_Chan)
		t := new(ChanType)
		t.pos = pos
		t.Dir = RecvOnly
		t.Elem = p.chanElem()
		return t

	case _Func:
		// fntype
		p.next()
		return p.funcType("function type", nil)

	case _Lbrack:
		// '[' oexpr ']' ntype
		// '[' _DotDotDot ']' ntype
		open := p.tapepos
		p.next()
		if p.got(_Rbrack) {
			p.checkLinks(open)
			return p.sliceType(pos)
		}
		return p.arrayType(open, pos, nil)

	case _Chan:
		// _Chan non_recvchantype
		// _Chan _Comm ntype
		p.next()
		t := new(ChanType)
		t.pos = pos
		if p.got(_Arrow) {
			t.Dir = SendOnly
		}
		t.Elem = p.chanElem()
		return t

	case _Map:
		// _Map '[' ntype ']' ntype
		p.next()
		p.want(_Lbrack)
		t := new(MapType)
		t.pos = pos
		t.Key = p.type_()
		p.want(_Rbrack)
		t.Value = p.type_()
		return t

	case _Struct:
		return p.structType()

	case _Interface:
		return p.interfaceType()

	case _Name:
		return p.qualifiedName(nil)

	case _Lparen:
		p.next()
		t := p.type_()
		p.want(_Rparen)
		return t
	}

	return nil
}

func (p *parser) typeInstance(typ Expr) Expr {
	if trace {
		defer p.trace("typeInstance")()
	}

	pos := p.pos()
	p.want(_Lbrack)
	x := new(IndexExpr)
	x.pos = pos
	x.X = typ
	if p.tok == _Rbrack {
		p.syntaxError("expecting type")
		x.Index = p.badExpr()
	} else {
		x.Index, _ = p.typeList()
	}
	p.want(_Rbrack)
	return x
}

// If context != "", type parameters are not permitted.
func (p *parser) funcType(context string, tparamList *[]*Field) *FuncType {
	if trace {
		defer p.trace("funcType")()
	}

	typ := new(FuncType)
	typ.pos = p.pos()

	if p.allowGenerics() && p.tok == _Lbrack {
		p.async(func() {
			p.next()
			if context != "" {
				// accept but complain
				p.syntaxErrorAt(typ.pos, context+" must have no type parameters")
			}
			if p.tok == _Rbrack {
				p.syntaxError("empty type parameter list")
				p.next()
			} else {
				list := p.paramList(nil, nil, _Rbrack, true)
				if tparamList != nil {
					*tparamList = list
				}
			}
		})
	}

	p.async(func() {
		p.want(_Lparen)
		typ.ParamList = p.paramList(nil, nil, _Rparen, false)
	})
	typ.ResultList = p.funcResult()

	return typ
}

// "[" has already been consumed, and pos is its position, and open is its tape index.
// If len != nil it is the already consumed array length.
func (p *parser) arrayType(open int, pos Pos, len Expr) Expr {
	if trace {
		defer p.trace("arrayType")()
	}

	if len == nil && !p.got(_DotDotDot) {
		p.xnest++
		len = p.expr()
		p.xnest--
	}
	if p.tok == _Comma {
		// Trailing commas are accepted in type parameter
		// lists but not in array type declarations.
		// Accept for better error handling but complain.
		p.syntaxError("unexpected comma; expecting ]")
		p.next()
	}
	p.want(_Rbrack)
	p.checkLinks(open)
	t := new(ArrayType)
	t.pos = pos
	t.Len = len
	t.Elem = p.type_()
	return t
}

// "[" and "]" have already been consumed, and pos is the position of "[".
func (p *parser) sliceType(pos Pos) Expr {
	t := new(SliceType)
	t.pos = pos
	t.Elem = p.type_()
	return t
}

func (p *parser) chanElem() Expr {
	if trace {
		defer p.trace("chanElem")()
	}

	typ := p.typeOrNil()
	if typ == nil {
		typ = p.badExpr()
		p.syntaxError("missing channel element type")
		// assume element type is simply absent - don't advance
	}

	return typ
}

// StructType = "struct" "{" { FieldDecl ";" } "}" .
func (p *parser) structType() *StructType {
	if trace {
		defer p.trace("structType")()
	}

	typ := new(StructType)
	typ.pos = p.pos()

	p.want(_Struct)
	p.asyncList(_Lbrace, _Semi, _Rbrace, func() bool {
		p.fieldDecl(typ)
		return false
	})

	return typ
}

// InterfaceType = "interface" "{" { ( MethodDecl | EmbeddedElem | TypeList ) ";" } "}" .
// TypeList      = "type" Type { "," Type } .
// TODO(gri) remove TypeList syntax if we accept #45346
func (p *parser) interfaceType() *InterfaceType {
	if trace {
		defer p.trace("interfaceType")()
	}

	typ := new(InterfaceType)
	typ.pos = p.pos()

	p.want(_Interface)
	p.asyncList(_Lbrace, _Semi, _Rbrace, func() bool {
		switch p.tok {
		case _Name:
			f := p.methodDecl()
			if f.Name == nil && p.allowGenerics() {
				f = p.embeddedElem(f)
			}
			typ.MethodList = append(typ.MethodList, f)
			return false

		case _Lparen:
			// TODO(gri) Need to decide how to adjust this restriction.
			p.syntaxError("cannot parenthesize embedded type")
			f := new(Field)
			f.pos = p.pos()
			p.next()
			f.Type = p.qualifiedName(nil)
			p.want(_Rparen)
			typ.MethodList = append(typ.MethodList, f)
			return false

		case _Operator:
			if p.op == Tilde && p.allowGenerics() {
				typ.MethodList = append(typ.MethodList, p.embeddedElem(nil))
				return false
			}

		default:
			if p.allowGenerics() {
				pos := p.pos()
				if t := p.typeOrNil(); t != nil {
					f := new(Field)
					f.pos = pos
					f.Type = t
					typ.MethodList = append(typ.MethodList, p.embeddedElem(f))
					return false
				}
			}
		}

		if p.allowGenerics() {
			p.syntaxError("expecting method or embedded element")
			p.advance(_Semi, _Rbrace)
			return false
		}

		p.syntaxError("expecting method or interface name")
		p.advance(_Semi, _Rbrace)
		return false
	})

	return typ
}

// Result = Parameters | Type .
func (p *parser) funcResult() []*Field {
	if trace {
		defer p.trace("funcResult")()
	}

	open := p.tapepos
	if p.got(_Lparen) {
		res := p.paramList(nil, nil, _Rparen, false)
		p.checkLinks(open)
		return res
	}

	pos := p.pos()
	if typ := p.typeOrNil(); typ != nil {
		f := new(Field)
		f.pos = pos
		f.Type = typ
		return []*Field{f}
	}

	return nil
}

func (p *parser) addField(styp *StructType, pos Pos, name *Name, typ Expr, tag *BasicLit) {
	if tag != nil {
		for i := len(styp.FieldList) - len(styp.TagList); i > 0; i-- {
			styp.TagList = append(styp.TagList, nil)
		}
		styp.TagList = append(styp.TagList, tag)
	}

	f := new(Field)
	f.pos = pos
	f.Name = name
	f.Type = typ
	styp.FieldList = append(styp.FieldList, f)

	if debug && tag != nil && len(styp.FieldList) != len(styp.TagList) {
		panic("inconsistent struct field list")
	}
}

// FieldDecl      = (IdentifierList Type | AnonymousField) [ Tag ] .
// AnonymousField = [ "*" ] TypeName .
// Tag            = string_lit .
func (p *parser) fieldDecl(styp *StructType) {
	if trace {
		defer p.trace("fieldDecl")()
	}

	pos := p.pos()
	switch p.tok {
	case _Name:
		name := p.name()
		if p.tok == _Dot || p.tok == _Literal || p.tok == _Semi || p.tok == _Rbrace {
			// embedded type
			typ := p.qualifiedName(name)
			tag := p.oliteral()
			p.addField(styp, pos, nil, typ, tag)
			break
		}

		// name1, name2, ... Type [ tag ]
		names := p.nameList(name)
		var typ Expr

		// Careful dance: We don't know if we have an embedded instantiated
		// type T[P1, P2, ...] or a field T of array/slice type [P]E or []E.
		if p.allowGenerics() && len(names) == 1 && p.tok == _Lbrack {
			typ = p.arrayOrTArgs()
			if typ, ok := typ.(*IndexExpr); ok {
				// embedded type T[P1, P2, ...]
				typ.X = name // name == names[0]
				tag := p.oliteral()
				p.addField(styp, pos, nil, typ, tag)
				break
			}
		} else {
			// T P
			typ = p.type_()
		}

		tag := p.oliteral()

		for _, name := range names {
			p.addField(styp, name.Pos(), name, typ, tag)
		}

	case _Star:
		p.next()
		var typ Expr
		if p.tok == _Lparen {
			// *(T)
			p.syntaxError("cannot parenthesize embedded type")
			p.next()
			typ = p.qualifiedName(nil)
			p.got(_Rparen) // no need to complain if missing
		} else {
			// *T
			typ = p.qualifiedName(nil)
		}
		tag := p.oliteral()
		p.addField(styp, pos, nil, newIndirect(pos, typ), tag)

	case _Lparen:
		p.syntaxError("cannot parenthesize embedded type")
		p.next()
		var typ Expr
		if p.tok == _Star {
			// (*T)
			pos := p.pos()
			p.next()
			typ = newIndirect(pos, p.qualifiedName(nil))
		} else {
			// (T)
			typ = p.qualifiedName(nil)
		}
		p.got(_Rparen) // no need to complain if missing
		tag := p.oliteral()
		p.addField(styp, pos, nil, typ, tag)

	default:
		p.syntaxError("expecting field name or embedded type")
		p.advance(_Semi, _Rbrace)
	}
}

func (p *parser) arrayOrTArgs() Expr {
	if trace {
		defer p.trace("arrayOrTArgs")()
	}

	pos := p.pos()
	p.want(_Lbrack)
	if p.got(_Rbrack) {
		return p.sliceType(pos)
	}

	// x [n]E or x[n,], x[n1, n2], ...
	n, comma := p.typeList()
	p.want(_Rbrack)
	if !comma {
		if elem := p.typeOrNil(); elem != nil {
			// x [n]E
			t := new(ArrayType)
			t.pos = pos
			t.Len = n
			t.Elem = elem
			return t
		}
	}

	// x[n,], x[n1, n2], ...
	t := new(IndexExpr)
	t.pos = pos
	// t.X will be filled in by caller
	t.Index = n
	return t
}

func (p *parser) oliteral() *BasicLit {
	if p.tok == _Literal {
		b := new(BasicLit)
		b.pos = p.pos()
		b.Value = p.lit
		b.Kind = p.kind
		b.Bad = p.bad
		p.next()
		return b
	}
	return nil
}

// MethodSpec        = MethodName Signature | InterfaceTypeName .
// MethodName        = identifier .
// InterfaceTypeName = TypeName .
func (p *parser) methodDecl() *Field {
	if trace {
		defer p.trace("methodDecl")()
	}

	f := new(Field)
	f.pos = p.pos()
	name := p.name()

	// accept potential name list but complain
	// TODO(gri) We probably don't need this special check anymore.
	//           Nobody writes this kind of code. It's from ancient
	//           Go beginnings.
	hasNameList := false
	for p.got(_Comma) {
		p.name()
		hasNameList = true
	}
	if hasNameList {
		p.syntaxError("name list not allowed in interface type")
		// already progressed, no need to advance
	}

	const context = "interface method"

	switch p.tok {
	case _Lparen:
		// method
		f.Name = name
		f.Type = p.funcType(context, nil)

	case _Lbrack:
		if p.allowGenerics() {
			// Careful dance: We don't know if we have a generic method m[T C](x T)
			// or an embedded instantiated type T[P1, P2] (we accept generic methods
			// for generality and robustness of parsing).
			pos := p.pos()
			p.next()

			// Empty type parameter or argument lists are not permitted.
			// Treat as if [] were absent.
			if p.tok == _Rbrack {
				// name[]
				pos := p.pos()
				p.next()
				if p.tok == _Lparen {
					// name[](
					p.errorAt(pos, "empty type parameter list")
					f.Name = name
					f.Type = p.funcType(context, nil)
				} else {
					p.errorAt(pos, "empty type argument list")
					f.Type = name
				}
				break
			}

			// A type argument list looks like a parameter list with only
			// types. Parse a parameter list and decide afterwards.
			list := p.paramList(nil, nil, _Rbrack, false)
			if len(list) == 0 {
				// The type parameter list is not [] but we got nothing
				// due to other errors (reported by paramList). Treat
				// as if [] were absent.
				if p.tok == _Lparen {
					f.Name = name
					f.Type = p.funcType(context, nil)
				} else {
					f.Type = name
				}
				break
			}

			// len(list) > 0
			if list[0].Name != nil {
				// generic method
				f.Name = name
				f.Type = p.funcType(context, nil)
				// TODO(gri) Record list as type parameter list with f.Type
				//           if we want to type-check the generic method.
				//           For now, report an error so this is not a silent event.
				p.errorAt(pos, "interface method must have no type parameters")
				break
			}

			// embedded instantiated type
			t := new(IndexExpr)
			t.pos = pos
			t.X = name
			if len(list) == 1 {
				t.Index = list[0].Type
			} else {
				// len(list) > 1
				l := new(ListExpr)
				l.pos = list[0].Pos()
				l.ElemList = make([]Expr, len(list))
				for i := range list {
					l.ElemList[i] = list[i].Type
				}
				t.Index = l
			}
			f.Type = t
			break
		}
		fallthrough

	default:
		// embedded type
		f.Type = p.qualifiedName(name)
	}

	return f
}

// EmbeddedElem = MethodSpec | EmbeddedTerm { "|" EmbeddedTerm } .
func (p *parser) embeddedElem(f *Field) *Field {
	if trace {
		defer p.trace("embeddedElem")()
	}

	if f == nil {
		f = new(Field)
		f.pos = p.pos()
		f.Type = p.embeddedTerm()
	}

	for p.tok == _Operator && p.op == Or {
		t := new(Operation)
		t.pos = p.pos()
		t.Op = Or
		p.next()
		t.X = f.Type
		t.Y = p.embeddedTerm()
		f.Type = t
	}

	return f
}

// EmbeddedTerm = [ "~" ] Type .
func (p *parser) embeddedTerm() Expr {
	if trace {
		defer p.trace("embeddedTerm")()
	}

	if p.tok == _Operator && p.op == Tilde {
		t := new(Operation)
		t.pos = p.pos()
		t.Op = Tilde
		p.next()
		t.X = p.type_()
		return t
	}

	t := p.typeOrNil()
	if t == nil {
		t = p.badExpr()
		p.syntaxError("expecting ~ term or type")
		p.advance(_Operator, _Semi, _Rparen, _Rbrack, _Rbrace)
	}

	return t
}

// ParameterDecl = [ IdentifierList ] [ "..." ] Type .
func (p *parser) paramDeclOrNil(name *Name, follow token) *Field {
	if trace {
		defer p.trace("paramDeclOrNil")()
	}

	// type set notation is ok in type parameter lists
	typeSetsOk := follow == _Rbrack

	pos := p.pos()
	if name != nil {
		pos = name.pos
	} else if typeSetsOk && p.tok == _Operator && p.op == Tilde {
		// "~" ...
		return p.embeddedElem(nil)
	}

	f := new(Field)
	f.pos = pos

	if p.tok == _Name || name != nil {
		// name
		if name == nil {
			name = p.name()
		}

		if p.allowGenerics() && p.tok == _Lbrack {
			// name "[" ...
			f.Type = p.arrayOrTArgs()
			if typ, ok := f.Type.(*IndexExpr); ok {
				// name "[" ... "]"
				typ.X = name
			} else {
				// name "[" n "]" E
				f.Name = name
			}
			if typeSetsOk && p.tok == _Operator && p.op == Or {
				// name "[" ... "]" "|" ...
				// name "[" n "]" E "|" ...
				f = p.embeddedElem(f)
			}
			return f
		}

		if p.tok == _Dot {
			// name "." ...
			f.Type = p.qualifiedName(name)
			if typeSetsOk && p.tok == _Operator && p.op == Or {
				// name "." name "|" ...
				f = p.embeddedElem(f)
			}
			return f
		}

		if typeSetsOk && p.tok == _Operator && p.op == Or {
			// name "|" ...
			f.Type = name
			return p.embeddedElem(f)
		}

		f.Name = name
	}

	if p.tok == _DotDotDot {
		// [name] "..." ...
		t := new(DotsType)
		t.pos = p.pos()
		p.next()
		t.Elem = p.typeOrNil()
		if t.Elem == nil {
			t.Elem = p.badExpr()
			p.syntaxError("... is missing type")
		}
		f.Type = t
		return f
	}

	if typeSetsOk && p.tok == _Operator && p.op == Tilde {
		// [name] "~" ...
		f.Type = p.embeddedElem(nil).Type
		return f
	}

	f.Type = p.typeOrNil()
	if typeSetsOk && p.tok == _Operator && p.op == Or && f.Type != nil {
		// [name] type "|"
		f = p.embeddedElem(f)
	}
	if f.Name != nil || f.Type != nil {
		return f
	}

	p.syntaxError("expecting " + tokstring(follow))
	p.advance(_Comma, follow)
	return nil
}

// Parameters    = "(" [ ParameterList [ "," ] ] ")" .
// ParameterList = ParameterDecl { "," ParameterDecl } .
// "(" or "[" has already been consumed.
// If name != nil, it is the first name after "(" or "[".
// If typ != nil, name must be != nil, and (name, typ) is the first field in the list.
// In the result list, either all fields have a name, or no field has a name.
func (p *parser) paramList(name *Name, typ Expr, close token, requireNames bool) (list []*Field) {
	if trace {
		defer p.trace("paramList")()
	}

	// p.list won't invoke its function argument if we're at the end of the
	// parameter list. If we have a complete field, handle this case here.
	if name != nil && typ != nil && p.tok == close {
		p.next()
		par := new(Field)
		par.pos = name.pos
		par.Name = name
		par.Type = typ
		return []*Field{par}
	}

	var named int // number of parameters that have an explicit name and type
	var typed int // number of parameters that have an explicit type
	end := p.list(_Comma, close, func() bool {
		var par *Field
		if typ != nil {
			if debug && name == nil {
				panic("initial type provided without name")
			}
			par = new(Field)
			par.pos = name.pos
			par.Name = name
			par.Type = typ
		} else {
			par = p.paramDeclOrNil(name, close)
		}
		name = nil // 1st name was consumed if present
		typ = nil  // 1st type was consumed if present
		if par != nil {
			if debug && par.Name == nil && par.Type == nil {
				panic("parameter without name or type")
			}
			if par.Name != nil && par.Type != nil {
				named++
			}
			if par.Type != nil {
				typed++
			}
			list = append(list, par)
		}
		return false
	})

	if len(list) == 0 {
		return
	}

	// distribute parameter types (len(list) > 0)
	if named == 0 && !requireNames {
		// all unnamed => found names are named types
		for _, par := range list {
			if typ := par.Name; typ != nil {
				par.Type = typ
				par.Name = nil
			}
		}
	} else if named != len(list) {
		// some named => all must have names and types
		var pos Pos  // left-most error position (or unknown)
		var typ Expr // current type (from right to left)
		for i := len(list) - 1; i >= 0; i-- {
			par := list[i]
			if par.Type != nil {
				typ = par.Type
				if par.Name == nil {
					pos = StartPos(typ)
					par.Name = NewName(pos, "_")
				}
			} else if typ != nil {
				par.Type = typ
			} else {
				// par.Type == nil && typ == nil => we only have a par.Name
				pos = par.Name.Pos()
				t := p.badExpr()
				t.pos = pos // correct position
				par.Type = t
			}
		}
		if pos.IsKnown() {
			var msg string
			if requireNames {
				if named == typed {
					pos = end // position error at closing ]
					msg = "missing type constraint"
				} else {
					msg = "type parameters must be named"
				}
			} else {
				msg = "mixed named and unnamed parameters"
			}
			p.syntaxErrorAt(pos, msg)
		}
	}

	return
}

func (p *parser) badExpr() *BadExpr {
	b := new(BadExpr)
	b.pos = p.pos()
	return b
}

// ----------------------------------------------------------------------------
// Statements

// SimpleStmt = EmptyStmt | ExpressionStmt | SendStmt | IncDecStmt | Assignment | ShortVarDecl .
func (p *parser) simpleStmt(lhs Expr, keyword token) SimpleStmt {
	if trace {
		defer p.trace("simpleStmt")()
	}

	if keyword == _For && p.tok == _Range {
		// _Range expr
		if debug && lhs != nil {
			panic("invalid call of simpleStmt")
		}
		return p.newRangeClause(nil, false)
	}

	if lhs == nil {
		lhs = p.exprList()
	}

	if _, ok := lhs.(*ListExpr); !ok && p.tok != _Assign && p.tok != _Define {
		// expr
		pos := p.pos()
		switch p.tok {
		case _AssignOp:
			// lhs op= rhs
			op := p.op
			p.next()
			return p.newAssignStmt(pos, op, lhs, p.expr())

		case _IncOp:
			// lhs++ or lhs--
			op := p.op
			p.next()
			return p.newAssignStmt(pos, op, lhs, nil)

		case _Arrow:
			// lhs <- rhs
			s := new(SendStmt)
			s.pos = pos
			p.next()
			s.Chan = lhs
			s.Value = p.expr()
			return s

		default:
			// expr
			s := new(ExprStmt)
			s.pos = lhs.Pos()
			s.X = lhs
			return s
		}
	}

	// expr_list
	switch p.tok {
	case _Assign, _Define:
		pos := p.pos()
		var op Operator
		if p.tok == _Define {
			op = Def
		}
		p.next()

		if keyword == _For && p.tok == _Range {
			// expr_list op= _Range expr
			return p.newRangeClause(lhs, op == Def)
		}

		// expr_list op= expr_list
		rhs := p.exprList()

		if x, ok := rhs.(*TypeSwitchGuard); ok && keyword == _Switch && op == Def {
			if lhs, ok := lhs.(*Name); ok {
				// switch … lhs := rhs.(type)
				x.Lhs = lhs
				s := new(ExprStmt)
				s.pos = x.Pos()
				s.X = x
				return s
			}
		}

		return p.newAssignStmt(pos, op, lhs, rhs)

	default:
		p.syntaxError("expecting := or = or comma")
		p.advance(_Semi, _Rbrace)
		// make the best of what we have
		if x, ok := lhs.(*ListExpr); ok {
			lhs = x.ElemList[0]
		}
		s := new(ExprStmt)
		s.pos = lhs.Pos()
		s.X = lhs
		return s
	}
}

func (p *parser) newRangeClause(lhs Expr, def bool) *RangeClause {
	r := new(RangeClause)
	r.pos = p.pos()
	p.next() // consume _Range
	r.Lhs = lhs
	r.Def = def
	r.X = p.expr()
	return r
}

func (p *parser) newAssignStmt(pos Pos, op Operator, lhs, rhs Expr) *AssignStmt {
	a := new(AssignStmt)
	a.pos = pos
	a.Op = op
	a.Lhs = lhs
	a.Rhs = rhs
	return a
}

func (p *parser) labeledStmtOrNil(label *Name) Stmt {
	if trace {
		defer p.trace("labeledStmt")()
	}

	s := new(LabeledStmt)
	s.pos = p.pos()
	s.Label = label

	p.want(_Colon)

	if p.tok == _Rbrace {
		// We expect a statement (incl. an empty statement), which must be
		// terminated by a semicolon. Because semicolons may be omitted before
		// an _Rbrace, seeing an _Rbrace implies an empty statement.
		e := new(EmptyStmt)
		e.pos = p.pos()
		s.Stmt = e
		return s
	}

	s.Stmt = p.stmtOrNil()
	if s.Stmt != nil {
		return s
	}

	// report error at line of ':' token
	p.syntaxErrorAt(s.pos, "missing statement after label")
	// we are already at the end of the labeled statement - no need to advance
	return nil // avoids follow-on errors (see e.g., fixedbugs/bug274.go)
}

// context must be a non-empty string unless we know that p.tok == _Lbrace.
func (p *parser) blockStmt(context string) *BlockStmt {
	if trace {
		defer p.trace("blockStmt")()
	}

	s := new(BlockStmt)
	s.pos = p.pos()

	p.async(func() {
		// people coming from C may forget that braces are mandatory in Go
		if !p.got(_Lbrace) {
			p.syntaxError("missing { after " + context)
			p.advance(_Name, _Rbrace)
			if p.got(_Rbrace) {
				return
			}
		}

		s.List = p.stmtList()
		s.Rbrace = p.pos()
		p.want(_Rbrace)
	})

	return s
}

func (p *parser) declStmt() *DeclStmt {
	if trace {
		defer p.trace("declStmt")()
	}

	s := new(DeclStmt)
	s.pos = p.pos()
	s.Decl = p.genDecl()

	return s
}

func (p *parser) forStmt() Stmt {
	if trace {
		defer p.trace("forStmt")()
	}

	s := new(ForStmt)
	s.pos = p.pos()

	s.Init, s.Cond, s.Post = p.header(_For)
	s.Body = p.blockStmt("for clause")

	return s
}

func (p *parser) header(keyword token) (init SimpleStmt, cond Expr, post SimpleStmt) {
	p.want(keyword)

	if p.tok == _Lbrace {
		if keyword == _If {
			p.syntaxError("missing condition in if statement")
			cond = p.badExpr()
		}
		return
	}
	// p.tok != _Lbrace

	outer := p.xnest
	p.xnest = -1

	if p.tok != _Semi {
		// accept potential varDecl but complain
		if p.got(_Var) {
			p.syntaxError(fmt.Sprintf("var declaration not allowed in %s initializer", tokstring(keyword)))
		}
		init = p.simpleStmt(nil, keyword)
		// If we have a range clause, we are done (can only happen for keyword == _For).
		if _, ok := init.(*RangeClause); ok {
			p.xnest = outer
			return
		}
	}

	var condStmt SimpleStmt
	var semi struct {
		pos Pos
		lit string // valid if pos.IsKnown()
	}
	if p.tok != _Lbrace {
		if p.tok == _Semi {
			semi.pos = p.pos()
			semi.lit = p.lit
			p.next()
		} else {
			// asking for a '{' rather than a ';' here leads to a better error message
			p.want(_Lbrace)
			if p.tok != _Lbrace {
				p.advance(_Lbrace, _Rbrace) // for better synchronization (e.g., issue #22581)
			}
		}
		if keyword == _For {
			if p.tok != _Semi {
				if p.tok == _Lbrace {
					p.syntaxError("expecting for loop condition")
					goto done
				}
				condStmt = p.simpleStmt(nil, 0 /* range not permitted */)
			}
			p.want(_Semi)
			if p.tok != _Lbrace {
				post = p.simpleStmt(nil, 0 /* range not permitted */)
				if a, _ := post.(*AssignStmt); a != nil && a.Op == Def {
					p.syntaxErrorAt(a.Pos(), "cannot declare in post statement of for loop")
				}
			}
		} else if p.tok != _Lbrace {
			condStmt = p.simpleStmt(nil, keyword)
		}
	} else {
		condStmt = init
		init = nil
	}

done:
	// unpack condStmt
	switch s := condStmt.(type) {
	case nil:
		if keyword == _If && semi.pos.IsKnown() {
			if semi.lit != "semicolon" {
				p.syntaxErrorAt(semi.pos, fmt.Sprintf("unexpected %s, expecting { after if clause", semi.lit))
			} else {
				p.syntaxErrorAt(semi.pos, "missing condition in if statement")
			}
			b := new(BadExpr)
			b.pos = semi.pos
			cond = b
		}
	case *ExprStmt:
		cond = s.X
	default:
		// A common syntax error is to write '=' instead of '==',
		// which turns an expression into an assignment. Provide
		// a more explicit error message in that case to prevent
		// further confusion.
		var str string
		if as, ok := s.(*AssignStmt); ok && as.Op == 0 {
			// Emphasize Lhs and Rhs of assignment with parentheses to highlight '='.
			// Do it always - it's not worth going through the trouble of doing it
			// only for "complex" left and right sides.
			str = "assignment (" + NodeString(as.Lhs) + ") = (" + NodeString(as.Rhs) + ")"
		} else {
			str = NodeString(s)
		}
		p.syntaxErrorAt(s.Pos(), fmt.Sprintf("cannot use %s as value", str))
	}

	p.xnest = outer
	return
}

func (p *parser) ifStmt() *IfStmt {
	if trace {
		defer p.trace("ifStmt")()
	}

	s := new(IfStmt)
	s.pos = p.pos()

	s.Init, s.Cond, _ = p.header(_If)
	s.Then = p.blockStmt("if clause")

	if p.got(_Else) {
		switch p.tok {
		case _If:
			s.Else = p.ifStmt()
		case _Lbrace:
			s.Else = p.blockStmt("")
		default:
			p.syntaxError("else must be followed by if or statement block")
			p.advance(_Name, _Rbrace)
		}
	}

	return s
}

func (p *parser) switchStmt() *SwitchStmt {
	if trace {
		defer p.trace("switchStmt")()
	}

	s := new(SwitchStmt)
	s.pos = p.pos()

	s.Init, s.Tag, _ = p.header(_Switch)

	p.async(func() {
		if !p.got(_Lbrace) {
			p.syntaxError("missing { after switch clause")
			p.advance(_Case, _Default, _Rbrace)
		}
		for p.tok != _EOF && p.tok != _Rbrace {
			s.Body = append(s.Body, p.caseClause())
		}
		s.Rbrace = p.pos()
		p.want(_Rbrace)
	})

	return s
}

func (p *parser) selectStmt() *SelectStmt {
	if trace {
		defer p.trace("selectStmt")()
	}

	s := new(SelectStmt)
	s.pos = p.pos()

	p.want(_Select)
	p.async(func() {
		if !p.got(_Lbrace) {
			p.syntaxError("missing { after select clause")
			p.advance(_Case, _Default, _Rbrace)
		}
		for p.tok != _EOF && p.tok != _Rbrace {
			s.Body = append(s.Body, p.commClause())
		}
		s.Rbrace = p.pos()
		p.want(_Rbrace)
	})

	return s
}

func (p *parser) caseClause() *CaseClause {
	if trace {
		defer p.trace("caseClause")()
	}

	c := new(CaseClause)
	c.pos = p.pos()

	switch p.tok {
	case _Case:
		p.next()
		c.Cases = p.exprList()

	case _Default:
		p.next()

	default:
		p.syntaxError("expecting case or default or }")
		p.advance(_Colon, _Case, _Default, _Rbrace)
	}

	c.Colon = p.pos()
	p.want(_Colon)
	c.Body = p.stmtList()

	return c
}

func (p *parser) commClause() *CommClause {
	if trace {
		defer p.trace("commClause")()
	}

	c := new(CommClause)
	c.pos = p.pos()

	switch p.tok {
	case _Case:
		p.next()
		c.Comm = p.simpleStmt(nil, 0)

		// The syntax restricts the possible simple statements here to:
		//
		//     lhs <- x (send statement)
		//     <-x
		//     lhs = <-x
		//     lhs := <-x
		//
		// All these (and more) are recognized by simpleStmt and invalid
		// syntax trees are flagged later, during type checking.
		// TODO(gri) eventually may want to restrict valid syntax trees
		// here.

	case _Default:
		p.next()

	default:
		p.syntaxError("expecting case or default or }")
		p.advance(_Colon, _Case, _Default, _Rbrace)
	}

	c.Colon = p.pos()
	p.want(_Colon)
	c.Body = p.stmtList()

	return c
}

// Statement =
// 	Declaration | LabeledStmt | SimpleStmt |
// 	GoStmt | ReturnStmt | BreakStmt | ContinueStmt | GotoStmt |
// 	FallthroughStmt | Block | IfStmt | SwitchStmt | SelectStmt | ForStmt |
// 	DeferStmt .
func (p *parser) stmtOrNil() Stmt {
	if trace {
		defer p.trace("stmt " + p.tok.String())()
	}

	// Most statements (assignments) start with an identifier;
	// look for it first before doing anything more expensive.
	if p.tok == _Name {
		p.clearPragma()
		lhs := p.exprList()
		if label, ok := lhs.(*Name); ok && p.tok == _Colon {
			return p.labeledStmtOrNil(label)
		}
		return p.simpleStmt(lhs, 0)
	}

	switch p.tok {
	case _Const, _Type, _Var:
		return p.declStmt()
	}

	p.clearPragma()

	switch p.tok {
	case _Lbrace:
		return p.blockStmt("")

	case _Operator, _Star:
		switch p.op {
		case Add, Sub, Mul, And, Xor, Not:
			return p.simpleStmt(nil, 0) // unary operators
		}

	case _Literal, _Func, _Lparen, // operands
		_Lbrack, _Struct, _Map, _Chan, _Interface, // composite types
		_Arrow: // receive operator
		return p.simpleStmt(nil, 0)

	case _For:
		return p.forStmt()

	case _Switch:
		return p.switchStmt()

	case _Select:
		return p.selectStmt()

	case _If:
		return p.ifStmt()

	case _Fallthrough:
		s := new(BranchStmt)
		s.pos = p.pos()
		p.next()
		s.Tok = _Fallthrough
		return s

	case _Break, _Continue:
		s := new(BranchStmt)
		s.pos = p.pos()
		s.Tok = p.tok
		p.next()
		if p.tok == _Name {
			s.Label = p.name()
		}
		return s

	case _Go, _Defer:
		return p.callStmt()

	case _Goto:
		s := new(BranchStmt)
		s.pos = p.pos()
		s.Tok = _Goto
		p.next()
		s.Label = p.name()
		return s

	case _Return:
		s := new(ReturnStmt)
		s.pos = p.pos()
		p.next()
		if p.tok != _Semi && p.tok != _Rbrace {
			s.Results = p.exprList()
		}
		return s

	case _Semi:
		s := new(EmptyStmt)
		s.pos = p.pos()
		return s
	}

	return nil
}

// StatementList = { Statement ";" } .
func (p *parser) stmtList() (l []Stmt) {
	if trace {
		defer p.trace("stmtList")()
	}

	for p.tok != _EOF && p.tok != _Rbrace && p.tok != _Case && p.tok != _Default {
		s := p.stmtOrNil()
		p.clearPragma()
		if s == nil {
			break
		}
		l = append(l, s)
		// ";" is optional before "}"
		if !p.got(_Semi) && p.tok != _Rbrace {
			p.syntaxError("at end of statement")
			p.advance(_Semi, _Rbrace, _Case, _Default)
			p.got(_Semi) // avoid spurious empty statement
		}
	}
	return
}

// ----------------------------------------------------------------------------
// Common productions

func (p *parser) name() *Name {
	// no tracing to avoid overly verbose output

	if p.tok == _Name {
		n := NewName(p.pos(), p.lit)
		p.next()
		return n
	}

	n := NewName(p.pos(), "_")
	p.syntaxError("expecting name")
	p.advance()
	return n
}

// IdentifierList = identifier { "," identifier } .
// The first name must be provided.
func (p *parser) nameList(first *Name) []*Name {
	if trace {
		defer p.trace("nameList")()
	}

	if debug && first == nil {
		panic("first name not provided")
	}

	l := []*Name{first}
	for p.got(_Comma) {
		l = append(l, p.name())
	}

	return l
}

// The first name may be provided, or nil.
func (p *parser) qualifiedName(name *Name) Expr {
	if trace {
		defer p.trace("qualifiedName")()
	}

	var x Expr
	switch {
	case name != nil:
		x = name
	case p.tok == _Name:
		x = p.name()
	default:
		x = NewName(p.pos(), "_")
		p.syntaxError("expecting name")
		p.advance(_Dot, _Semi, _Rbrace)
	}

	if p.tok == _Dot {
		s := new(SelectorExpr)
		s.pos = p.pos()
		p.next()
		s.X = x
		s.Sel = p.name()
		x = s
	}

	if p.allowGenerics() && p.tok == _Lbrack {
		x = p.typeInstance(x)
	}

	return x
}

// ExpressionList = Expression { "," Expression } .
func (p *parser) exprList() Expr {
	if trace {
		defer p.trace("exprList")()
	}

	x := p.expr()
	if p.got(_Comma) {
		list := []Expr{x, p.expr()}
		for p.got(_Comma) {
			list = append(list, p.expr())
		}
		t := new(ListExpr)
		t.pos = x.Pos()
		t.ElemList = list
		x = t
	}
	return x
}

// typeList parses a non-empty, comma-separated list of expressions,
// optionally followed by a comma. The first list element may be any
// expression, all other list elements must be type expressions.
// If there is more than one argument, the result is a *ListExpr.
// The comma result indicates whether there was a (separating or
// trailing) comma.
//
// typeList = arg { "," arg } [ "," ] .
func (p *parser) typeList() (x Expr, comma bool) {
	if trace {
		defer p.trace("typeList")()
	}

	p.xnest++
	x = p.expr()
	if p.got(_Comma) {
		comma = true
		if t := p.typeOrNil(); t != nil {
			list := []Expr{x, t}
			for p.got(_Comma) {
				if t = p.typeOrNil(); t == nil {
					break
				}
				list = append(list, t)
			}
			l := new(ListExpr)
			l.pos = x.Pos() // == list[0].Pos()
			l.ElemList = list
			x = l
		}
	}
	p.xnest--
	return
}

func (p *parser) asyncList(open, sep, close token, f func() bool) (Pos, Pos) {
	pos := p.pos()
	link := p.link

	// Bad syntax; eagerly parse.
	if p.tok != open || link < 0 || p.tape[link].tok != close {
		p.want(open)
		return pos, p.list(sep, close, f)
	}

	p.asyncCalls = append(p.asyncCalls, p.capture(func() {
		p.next() // skip open
		p.list(sep, close, f)
	}))

	for p.tapepos < link {
		p.next()
	}
	end := p.pos()
	p.next()

	return pos, end
}

func (p *parser) async(fn func())     { p.asyncOK(true, fn) }
func (p *parser) asyncTODO(fn func()) { p.asyncOK(false, fn) }

func (p *parser) asyncOK(allowAsync bool, fn func()) {
	call := p.capture(fn)
	close := p.link

	if close < 0 || !allowAsync {
		// Source syntax is not properly nested, so we don't know where to
		// seek to. Just parse eagerly instead.
		call.do(p)
		return
	}

	p.asyncCalls = append(p.asyncCalls, call)

	// Seek past closing token.
	//
	// TODO(mdempsky): Handle line directives during initial scan, so
	// that seeking takes O(1) time.
	for p.tapepos <= close {
		p.next()
	}
}

func (p *parser) checkLinks(open int) {
	// if there are syntax errors, then don't expect links to match up
	if p.errcnt != 0 {
		return
	}

	close := p.tapepos - 1

	// Rewind past any trailing comments.
	for p.tape[close].tok == _Error {
		close--
	}

	if p.tape[open].link != close || p.tape[close].link != open {
		panic(fmt.Errorf("checkLinks(%v, %v):\n\ttape[%v] = %#v\n\ttape[%v] = %#v", open, close, open, p.tape[open], close, p.tape[close]))
	}

	// TODO(mdempsky): Check that p.tape[open].tok and p.tape[close].tok match?
}

// Unparen removes all parentheses around an expression.
func Unparen(x Expr) Expr {
	for {
		p, ok := x.(*ParenExpr)
		if !ok {
			break
		}
		x = p.X
	}
	return x
}
