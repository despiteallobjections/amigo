// Copyright 2012 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// This file implements typechecking of statements.

package types

import (
	"go/constant"
	"sort"

	. "github.com/mdempsky/amigo/syntax"
)

func (check *Checker) funcBody(decl *declInfo, name string, sig *Signature, body *BlockStmt, iota constant.Value) {
	if check.conf.IgnoreFuncBodies {
		panic("function body not ignored")
	}

	if check.conf.Trace {
		check.trace(body.Pos(), "-- %s: %s", name, sig)
	}

	// set function scope extent
	sig.scope.pos = body.Pos()
	sig.scope.end = EndPos(body)

	// save/restore current environment and set up function environment
	// (and use 0 indentation at function start)
	defer func(env environment, indent int) {
		check.environment = env
		check.indent = indent
	}(check.environment, check.indent)
	check.environment = environment{
		decl:  decl,
		scope: sig.scope,
		iota:  iota,
		sig:   sig,
	}
	check.indent = 0

	check.stmtList(0, body.List)

	if check.hasLabel && !check.conf.IgnoreLabels {
		check.labels(body)
	}

	if sig.results.Len() > 0 && !check.isTerminating(body, "") {
		check.error(body.Rbrace, "missing return")
	}

	// spec: "Implementation restriction: A compiler may make it illegal to
	// declare a variable inside a function body if the variable is never used."
	check.usage(sig.scope)
}

func (check *Checker) usage(scope *Scope) {
	var unused []*Var
	for name, elem := range scope.elems {
		elem = resolve(name, elem)
		if v, _ := elem.(*Var); v != nil && !v.used {
			unused = append(unused, v)
		}
	}
	sort.Slice(unused, func(i, j int) bool {
		return unused[i].pos.Cmp(unused[j].pos) < 0
	})
	for _, v := range unused {
		check.softErrorf(v.pos, "%s declared but not used", v.name)
	}

	for _, scope := range scope.children {
		// Don't go inside function literal scopes a second time;
		// they are handled explicitly by funcBody.
		if !scope.isFunc {
			check.usage(scope)
		}
	}
}

// stmtContext is a bitset describing which
// control-flow statements are permissible,
// and provides additional context information
// for better error messages.
type stmtContext uint

const (
	// permissible control-flow statements
	breakOk stmtContext = 1 << iota
	continueOk
	fallthroughOk

	// additional context information
	finalSwitchCase
	inTypeSwitch
)

func (check *Checker) simpleStmt(s Stmt) {
	if s != nil {
		check.stmt(0, s)
	}
}

func trimTrailingEmptyStmts(list []Stmt) []Stmt {
	for i := len(list); i > 0; i-- {
		if _, ok := list[i-1].(*EmptyStmt); !ok {
			return list[:i]
		}
	}
	return nil
}

func (check *Checker) stmtList(ctxt stmtContext, list []Stmt) {
	ok := ctxt&fallthroughOk != 0
	inner := ctxt &^ fallthroughOk
	list = trimTrailingEmptyStmts(list) // trailing empty statements are "invisible" to fallthrough analysis
	for i, s := range list {
		inner := inner
		if ok && i+1 == len(list) {
			inner |= fallthroughOk
		}
		check.stmt(inner, s)
	}
}

func (check *Checker) multipleSwitchDefaults(list []*CaseClause) {
	var first *CaseClause
	for _, c := range list {
		if c.Cases == nil {
			if first != nil {
				check.errorf(c, "multiple defaults (first at %s)", first.Pos())
				// TODO(gri) probably ok to bail out after first error (and simplify this code)
			} else {
				first = c
			}
		}
	}
}

func (check *Checker) multipleSelectDefaults(list []*CommClause) {
	var first *CommClause
	for _, c := range list {
		if c.Comm == nil {
			if first != nil {
				check.errorf(c, "multiple defaults (first at %s)", first.Pos())
				// TODO(gri) probably ok to bail out after first error (and simplify this code)
			} else {
				first = c
			}
		}
	}
}

func (check *Checker) openScope(node Node, comment string) {
	check.openScopeUntil(node, EndPos(node), comment)
}

func (check *Checker) openScopeUntil(node Node, end Pos, comment string) {
	scope := NewScope(check.scope, node.Pos(), end, comment)
	check.recordScope(node, scope)
	check.scope = scope
}

func (check *Checker) closeScope() {
	check.scope = check.scope.Parent()
}

func (check *Checker) suspendedCall(keyword string, call *CallExpr) {
	var x operand
	var msg string
	switch check.rawExpr(&x, call, nil, false) {
	case conversion:
		msg = "requires function call, not conversion"
	case expression:
		msg = "discards result of"
	case statement:
		return
	default:
		unreachable()
	}
	check.errorf(&x, "%s %s %s", keyword, msg, &x)
}

// goVal returns the Go value for val, or nil.
func goVal(val constant.Value) interface{} {
	// val should exist, but be conservative and check
	if val == nil {
		return nil
	}
	// Match implementation restriction of other compilers.
	// gc only checks duplicates for integer, floating-point
	// and string values, so only create Go values for these
	// types.
	switch val.Kind() {
	case constant.Int:
		if x, ok := constant.Int64Val(val); ok {
			return x
		}
		if x, ok := constant.Uint64Val(val); ok {
			return x
		}
	case constant.Float:
		if x, ok := constant.Float64Val(val); ok {
			return x
		}
	case constant.String:
		return constant.StringVal(val)
	}
	return nil
}

// A valueMap maps a case value (of a basic Go type) to a list of positions
// where the same case value appeared, together with the corresponding case
// types.
// Since two case values may have the same "underlying" value but different
// types we need to also check the value's types (e.g., byte(1) vs myByte(1))
// when the switch expression is of interface type.
type (
	valueMap  map[interface{}][]valueType // underlying Go value -> valueType
	valueType struct {
		pos Pos
		typ Type
	}
)

func (check *Checker) caseValues(x *operand, values []Expr, seen valueMap) {
L:
	for _, e := range values {
		var v operand
		check.expr(&v, e)
		if x.mode == invalid || v.mode == invalid {
			continue L
		}
		check.convertUntyped(&v, x.typ)
		if v.mode == invalid {
			continue L
		}
		// Order matters: By comparing v against x, error positions are at the case values.
		res := v // keep original v unchanged
		check.comparison(&res, x, Eql, true)
		if res.mode == invalid {
			continue L
		}
		if v.mode != constant_ {
			continue L // we're done
		}
		// look for duplicate values
		if val := goVal(v.val); val != nil {
			// look for duplicate types for a given value
			// (quadratic algorithm, but these lists tend to be very short)
			for _, vt := range seen[val] {
				if Identical(v.typ, vt.typ) {
					var err error_
					err.errorf(&v, "duplicate case %s in expression switch", &v)
					err.errorf(vt.pos, "previous case")
					check.report(&err)
					continue L
				}
			}
			seen[val] = append(seen[val], valueType{v.Pos(), v.typ})
		}
	}
}

// isNil reports whether the expression e denotes the predeclared value nil.
func (check *Checker) isNil(e Expr) bool {
	// The only way to express the nil value is by literally writing nil (possibly in parentheses).
	if name, _ := Unparen(e).(*Name); name != nil {
		_, ok := check.lookup(name.Value).(*Nil)
		return ok
	}
	return false
}

// If the type switch expression is invalid, x is nil.
func (check *Checker) caseTypes(x *operand, types []Expr, seen map[Type]Expr) (T Type) {
	var dummy operand
L:
	for _, e := range types {
		// The spec allows the value nil instead of a type.
		if check.isNil(e) {
			T = nil
			check.expr(&dummy, e) // run e through expr so we get the usual Info recordings
		} else {
			T = check.varType(e)
			if T == Typ[Invalid] {
				continue L
			}
		}
		// look for duplicate types
		// (quadratic algorithm, but type switches tend to be reasonably small)
		for t, other := range seen {
			if T == nil && t == nil || T != nil && t != nil && Identical(T, t) {
				// talk about "case" rather than "type" because of nil case
				Ts := "nil"
				if T != nil {
					Ts = TypeString(T, check.qualifier)
				}
				var err error_
				err.errorf(e, "duplicate case %s in type switch", Ts)
				err.errorf(other, "previous case")
				check.report(&err)
				continue L
			}
		}
		seen[T] = e
		if x != nil && T != nil {
			check.typeAssertion(e, x, T, true)
		}
	}
	return
}

// TODO(gri) Once we are certain that typeHash is correct in all situations, use this version of caseTypes instead.
//           (Currently it may be possible that different types have identical names and import paths due to ImporterFrom.)
//
// func (check *Checker) caseTypes(x *operand, xtyp *Interface, types []syntax.Expr, seen map[string]syntax.Expr) (T Type) {
// 	var dummy operand
// L:
// 	for _, e := range types {
// 		// The spec allows the value nil instead of a type.
// 		var hash string
// 		if check.isNil(e) {
// 			check.expr(&dummy, e) // run e through expr so we get the usual Info recordings
// 			T = nil
// 			hash = "<nil>" // avoid collision with a type named nil
// 		} else {
// 			T = check.varType(e)
// 			if T == Typ[Invalid] {
// 				continue L
// 			}
// 			hash = typeHash(T, nil)
// 		}
// 		// look for duplicate types
// 		if other := seen[hash]; other != nil {
// 			// talk about "case" rather than "type" because of nil case
// 			Ts := "nil"
// 			if T != nil {
// 				Ts = TypeString(T, check.qualifier)
// 			}
// 			var err error_
// 			err.errorf(e, "duplicate case %s in type switch", Ts)
// 			err.errorf(other, "previous case")
// 			check.report(&err)
// 			continue L
// 		}
// 		seen[hash] = e
// 		if T != nil {
// 			check.typeAssertion(e, x, xtyp, T, true)
// 		}
// 	}
// 	return
// }

// stmt typechecks statement s.
func (check *Checker) stmt(ctxt stmtContext, s Stmt) {
	// statements must end with the same top scope as they started with
	if debug {
		defer func(scope *Scope) {
			// don't check if code is panicking
			if p := recover(); p != nil {
				panic(p)
			}
			assert(scope == check.scope)
		}(check.scope)
	}

	// process collected function literals before scope changes
	defer check.processDelayed(len(check.delayed))

	// reset context for statements of inner blocks
	inner := ctxt &^ (fallthroughOk | finalSwitchCase | inTypeSwitch)

	switch s := s.(type) {
	case *EmptyStmt:
		// ignore

	case *DeclStmt:
		check.declStmt(s.Decl)

	case *LabeledStmt:
		check.hasLabel = true
		check.stmt(ctxt, s.Stmt)

	case *ExprStmt:
		// spec: "With the exception of specific built-in functions,
		// function and method calls and receive operations can appear
		// in statement context. Such statements may be parenthesized."
		var x operand
		kind := check.rawExpr(&x, s.X, nil, false)
		var msg string
		switch x.mode {
		default:
			if kind == statement {
				return
			}
			msg = "is not used"
		case builtin:
			msg = "must be called"
		case typexpr:
			msg = "is not an expression"
		}
		check.errorf(&x, "%s %s", &x, msg)

	case *SendStmt:
		var ch, val operand
		check.expr(&ch, s.Chan)
		check.expr(&val, s.Value)
		if ch.mode == invalid || val.mode == invalid {
			return
		}
		u := coreType(ch.typ)
		if u == nil {
			check.errorf(s, invalidOp+"cannot send to %s: no core type", &ch)
			return
		}
		uch, _ := u.(*Chan)
		if uch == nil {
			check.errorf(s, invalidOp+"cannot send to non-channel %s", &ch)
			return
		}
		if uch.dir == RecvOnly {
			check.errorf(s, invalidOp+"cannot send to receive-only channel %s", &ch)
			return
		}
		check.assignment(&val, uch.elem, "send")

	case *AssignStmt:
		lhs := unpackExpr(s.Lhs)
		if s.Rhs == nil {
			// x++ or x--
			if len(lhs) != 1 {
				check.errorf(s, invalidAST+"%s%s requires one operand", s.Op, s.Op)
				return
			}
			var x operand
			check.expr(&x, lhs[0])
			if x.mode == invalid {
				return
			}
			if !allNumeric(x.typ) {
				check.errorf(lhs[0], invalidOp+"%s%s%s (non-numeric type %s)", lhs[0], s.Op, s.Op, x.typ)
				return
			}
			check.assignVar(lhs[0], &x)
			return
		}

		rhs := unpackExpr(s.Rhs)
		switch s.Op {
		case 0:
			check.assignVars(lhs, rhs)
			return
		case Def:
			check.shortVarDecl(s.Pos(), lhs, rhs)
			return
		}

		// assignment operations
		if len(lhs) != 1 || len(rhs) != 1 {
			check.errorf(s, "assignment operation %s requires single-valued expressions", s.Op)
			return
		}

		var x operand
		check.binary(&x, nil, lhs[0], rhs[0], s.Op)
		check.assignVar(lhs[0], &x)

	case *CallStmt:
		kind := "go"
		if s.Tok == Defer {
			kind = "defer"
		}
		check.suspendedCall(kind, s.Call)

	case *ReturnStmt:
		res := check.sig.results
		// Return with implicit results allowed for function with named results.
		// (If one is named, all are named.)
		results := unpackExpr(s.Results)
		if len(results) == 0 && res.Len() > 0 && res.vars[0].name != "" {
			// spec: "Implementation restriction: A compiler may disallow an empty expression
			// list in a "return" statement if a different entity (constant, type, or variable)
			// with the same name as a result parameter is in scope at the place of the return."
			for _, obj := range res.vars {
				if alt := check.lookup(obj.name); alt != nil && alt != obj {
					var err error_
					err.errorf(s, "result parameter %s not in scope at return", obj.name)
					err.errorf(alt, "inner declaration of %s", obj)
					check.report(&err)
					// ok to continue
				}
			}
		} else {
			var lhs []*Var
			if res.Len() > 0 {
				lhs = res.vars
			}
			check.initVars(lhs, results, s)
		}

	case *BranchStmt:
		if s.Label != nil {
			check.hasLabel = true
			break // checked in 2nd pass (check.labels)
		}
		switch s.Tok {
		case Break:
			if ctxt&breakOk == 0 {
				if check.conf.CompilerErrorMessages {
					check.error(s, "break is not in a loop, switch, or select statement")
				} else {
					check.error(s, "break not in for, switch, or select statement")
				}
			}
		case Continue:
			if ctxt&continueOk == 0 {
				if check.conf.CompilerErrorMessages {
					check.error(s, "continue is not in a loop")
				} else {
					check.error(s, "continue not in for statement")
				}
			}
		case Fallthrough:
			if ctxt&fallthroughOk == 0 {
				var msg string
				switch {
				case ctxt&finalSwitchCase != 0:
					msg = "cannot fallthrough final case in switch"
				case ctxt&inTypeSwitch != 0:
					msg = "cannot fallthrough in type switch"
				default:
					msg = "fallthrough statement out of place"
				}
				check.error(s, msg)
			}
		case Goto:
			// goto's must have labels, should have been caught above
			fallthrough
		default:
			check.errorf(s, invalidAST+"branch statement: %s", s.Tok)
		}

	case *BlockStmt:
		check.openScope(s, "block")
		defer check.closeScope()

		check.stmtList(inner, s.List)

	case *IfStmt:
		check.openScope(s, "if")
		defer check.closeScope()

		check.simpleStmt(s.Init)
		var x operand
		check.expr(&x, s.Cond)
		if x.mode != invalid && !allBoolean(x.typ) {
			check.error(s.Cond, "non-boolean condition in if statement")
		}
		check.stmt(inner, s.Then)
		// The parser produces a correct AST but if it was modified
		// elsewhere the else branch may be invalid. Check again.
		switch s.Else.(type) {
		case nil:
			// valid or error already reported
		case *IfStmt, *BlockStmt:
			check.stmt(inner, s.Else)
		default:
			check.error(s.Else, "invalid else branch in if statement")
		}

	case *SwitchStmt:
		inner |= breakOk
		check.openScope(s, "switch")
		defer check.closeScope()

		check.simpleStmt(s.Init)

		if g, _ := s.Tag.(*TypeSwitchGuard); g != nil {
			check.typeSwitchStmt(inner|inTypeSwitch, s, g)
		} else {
			check.switchStmt(inner, s)
		}

	case *SelectStmt:
		inner |= breakOk

		check.multipleSelectDefaults(s.Body)

		for i, clause := range s.Body {
			if clause == nil {
				continue // error reported before
			}

			// clause.Comm must be a SendStmt, RecvStmt, or default case
			valid := false
			var rhs Expr // rhs of RecvStmt, or nil
			switch s := clause.Comm.(type) {
			case nil, *SendStmt:
				valid = true
			case *AssignStmt:
				if _, ok := s.Rhs.(*ListExpr); !ok {
					rhs = s.Rhs
				}
			case *ExprStmt:
				rhs = s.X
			}

			// if present, rhs must be a receive operation
			if rhs != nil {
				if x, _ := Unparen(rhs).(*Operation); x != nil && x.Y == nil && x.Op == Recv {
					valid = true
				}
			}

			if !valid {
				check.error(clause.Comm, "select case must be send or receive (possibly with assignment)")
				continue
			}
			end := s.Rbrace
			if i+1 < len(s.Body) {
				end = s.Body[i+1].Pos()
			}
			check.openScopeUntil(clause, end, "case")
			if clause.Comm != nil {
				check.stmt(inner, clause.Comm)
			}
			check.stmtList(inner, clause.Body)
			check.closeScope()
		}

	case *ForStmt:
		inner |= breakOk | continueOk

		if rclause, _ := s.Init.(*RangeClause); rclause != nil {
			check.rangeStmt(inner, s, rclause)
			break
		}

		check.openScope(s, "for")
		defer check.closeScope()

		check.simpleStmt(s.Init)
		if s.Cond != nil {
			var x operand
			check.expr(&x, s.Cond)
			if x.mode != invalid && !allBoolean(x.typ) {
				check.error(s.Cond, "non-boolean condition in for statement")
			}
		}
		check.simpleStmt(s.Post)
		// spec: "The init statement may be a short variable
		// declaration, but the post statement must not."
		if s, _ := s.Post.(*AssignStmt); s != nil && s.Op == Def {
			// The parser already reported an error.
			check.use(s.Lhs) // avoid follow-up errors
		}
		check.stmt(inner, s.Body)

	default:
		check.error(s, "invalid statement")
	}
}

func (check *Checker) switchStmt(inner stmtContext, s *SwitchStmt) {
	// init statement already handled

	var x operand
	if s.Tag != nil {
		check.expr(&x, s.Tag)
		// By checking assignment of x to an invisible temporary
		// (as a compiler would), we get all the relevant checks.
		check.assignment(&x, nil, "switch expression")
		if x.mode != invalid && !Comparable(x.typ) && !hasNil(x.typ) {
			check.errorf(&x, "cannot switch on %s (%s is not comparable)", &x, x.typ)
			x.mode = invalid
		}
	} else {
		// spec: "A missing switch expression is
		// equivalent to the boolean value true."
		x.mode = constant_
		x.typ = Typ[Bool]
		x.val = constant.MakeBool(true)
		// TODO(gri) should have a better position here
		pos := s.Rbrace
		if len(s.Body) > 0 {
			pos = s.Body[0].Pos()
		}
		x.expr = NewName(pos, "true")
	}

	check.multipleSwitchDefaults(s.Body)

	seen := make(valueMap) // map of seen case values to positions and types
	for i, clause := range s.Body {
		if clause == nil {
			check.error(clause, invalidAST+"incorrect expression switch case")
			continue
		}
		end := s.Rbrace
		inner := inner
		if i+1 < len(s.Body) {
			end = s.Body[i+1].Pos()
			inner |= fallthroughOk
		} else {
			inner |= finalSwitchCase
		}
		check.caseValues(&x, unpackExpr(clause.Cases), seen)
		check.openScopeUntil(clause, end, "case")
		check.stmtList(inner, clause.Body)
		check.closeScope()
	}
}

func (check *Checker) typeSwitchStmt(inner stmtContext, s *SwitchStmt, guard *TypeSwitchGuard) {
	// init statement already handled

	// A type switch guard must be of the form:
	//
	//     TypeSwitchGuard = [ identifier ":=" ] PrimaryExpr "." "(" "type" ")" .
	//                          \__lhs__/        \___rhs___/

	// check lhs, if any
	lhs := guard.Lhs
	if lhs != nil {
		if lhs.Value == "_" {
			// _ := x.(type) is an invalid short variable declaration
			check.softErrorf(lhs, "no new variable on left side of :=")
			lhs = nil // avoid declared but not used error below
		} else {
			check.recordDef(lhs, nil) // lhs variable is implicitly declared in each cause clause
		}
	}

	// check rhs
	var x operand
	check.expr(&x, guard.X)
	if x.mode == invalid {
		return
	}

	// TODO(gri) we may want to permit type switches on type parameter values at some point
	var sx *operand // switch expression against which cases are compared against; nil if invalid
	if isTypeParam(x.typ) {
		check.errorf(&x, "cannot use type switch on type parameter value %s", &x)
	} else {
		if _, ok := under(x.typ).(*Interface); ok {
			sx = &x
		} else {
			check.errorf(&x, "%s is not an interface", &x)
		}
	}

	check.multipleSwitchDefaults(s.Body)

	var lhsVars []*Var          // list of implicitly declared lhs variables
	seen := make(map[Type]Expr) // map of seen types to positions
	for i, clause := range s.Body {
		if clause == nil {
			check.error(s, invalidAST+"incorrect type switch case")
			continue
		}
		end := s.Rbrace
		if i+1 < len(s.Body) {
			end = s.Body[i+1].Pos()
		}
		// Check each type in this type switch case.
		cases := unpackExpr(clause.Cases)
		T := check.caseTypes(sx, cases, seen)
		check.openScopeUntil(clause, end, "case")
		// If lhs exists, declare a corresponding variable in the case-local scope.
		if lhs != nil {
			// spec: "The TypeSwitchGuard may include a short variable declaration.
			// When that form is used, the variable is declared at the beginning of
			// the implicit block in each clause. In clauses with a case listing
			// exactly one type, the variable has that type; otherwise, the variable
			// has the type of the expression in the TypeSwitchGuard."
			if len(cases) != 1 || T == nil {
				T = x.typ
			}
			obj := NewVar(lhs.Pos(), check.pkg, lhs.Value, T)
			// TODO(mdempsky): Just use clause.Colon? Why did I even suggest
			// "at the end of the TypeSwitchCase" in #16794 instead?
			scopePos := clause.Pos() // for default clause (len(List) == 0)
			if n := len(cases); n > 0 {
				scopePos = EndPos(cases[n-1])
			}
			check.declare(check.scope, nil, obj, scopePos)
			check.recordImplicit(clause, obj)
			// For the "declared but not used" error, all lhs variables act as
			// one; i.e., if any one of them is 'used', all of them are 'used'.
			// Collect them for later analysis.
			lhsVars = append(lhsVars, obj)
		}
		check.stmtList(inner, clause.Body)
		check.closeScope()
	}

	// If lhs exists, we must have at least one lhs variable that was used.
	// (We can't use check.usage because that only looks at one scope; and
	// we don't want to use the same variable for all scopes and change the
	// variable type underfoot.)
	if lhs != nil {
		var used bool
		for _, v := range lhsVars {
			if v.used {
				used = true
			}
			v.used = true // avoid usage error when checking entire function
		}
		if !used {
			check.softErrorf(lhs, "%s declared but not used", lhs.Value)
		}
	}
}

func (check *Checker) rangeStmt(inner stmtContext, s *ForStmt, rclause *RangeClause) {
	// determine lhs, if any
	sKey := rclause.Lhs // possibly nil
	var sValue, sExtra Expr
	if p, _ := sKey.(*ListExpr); p != nil {
		if len(p.ElemList) < 2 {
			check.error(s, invalidAST+"invalid lhs in range clause")
			return
		}
		// len(p.ElemList) >= 2
		sKey = p.ElemList[0]
		sValue = p.ElemList[1]
		if len(p.ElemList) > 2 {
			// delay error reporting until we know more
			sExtra = p.ElemList[2]
		}
	}

	// check expression to iterate over
	var x operand
	check.expr(&x, rclause.X)

	// determine key/value types
	var key, val Type
	if x.mode != invalid {
		// Ranging over a type parameter is permitted if it has a core type.
		var cause string
		u := coreType(x.typ)
		if t, _ := u.(*Chan); t != nil {
			if sValue != nil {
				check.softErrorf(sValue, "range over %s permits only one iteration variable", &x)
				// ok to continue
			}
			if t.dir == SendOnly {
				cause = "receive from send-only channel"
			}
		} else {
			if sExtra != nil {
				check.softErrorf(sExtra, "range clause permits at most two iteration variables")
				// ok to continue
			}
			if u == nil {
				cause = check.sprintf("%s has no core type", x.typ)
			}
		}
		key, val = rangeKeyVal(u)
		if key == nil || cause != "" {
			if cause == "" {
				check.softErrorf(&x, "cannot range over %s", &x)
			} else {
				check.softErrorf(&x, "cannot range over %s (%s)", &x, cause)
			}
			// ok to continue
		}
	}

	// Open the for-statement block scope now, after the range clause.
	// Iteration variables declared with := need to go in this scope (was issue #51437).
	check.openScope(s, "range")
	defer check.closeScope()

	// check assignment to/declaration of iteration variables
	// (irregular assignment, cannot easily map to existing assignment checks)

	// lhs expressions and initialization value (rhs) types
	lhs := [2]Expr{sKey, sValue}
	rhs := [2]Type{key, val} // key, val may be nil

	if rclause.Def {
		// short variable declaration
		var vars []*Var
		for i, lhs := range lhs {
			if lhs == nil {
				continue
			}

			// determine lhs variable
			var obj *Var
			if ident, _ := lhs.(*Name); ident != nil {
				// declare new variable
				name := ident.Value
				obj = NewVar(ident.Pos(), check.pkg, name, nil)
				check.recordDef(ident, obj)
				// _ variables don't count as new variables
				if name != "_" {
					vars = append(vars, obj)
				}
			} else {
				check.errorf(lhs, "cannot declare %s", lhs)
				obj = NewVar(lhs.Pos(), check.pkg, "_", nil) // dummy variable
			}

			// initialize lhs variable
			if typ := rhs[i]; typ != nil {
				x.mode = value
				x.expr = lhs // we don't have a better rhs expression to use here
				x.typ = typ
				check.initVar(obj, &x, "range clause")
			} else {
				obj.typ = Typ[Invalid]
				obj.used = true // don't complain about unused variable
			}
		}

		// declare variables
		if len(vars) > 0 {
			scopePos := s.Body.Pos()
			for _, obj := range vars {
				check.declare(check.scope, nil /* recordDef already called */, obj, scopePos)
			}
		} else {
			check.error(s, "no new variables on left side of :=")
		}
	} else {
		// ordinary assignment
		for i, lhs := range lhs {
			if lhs == nil {
				continue
			}
			if typ := rhs[i]; typ != nil {
				x.mode = value
				x.expr = lhs // we don't have a better rhs expression to use here
				x.typ = typ
				check.assignVar(lhs, &x)
			}
		}
	}

	check.stmt(inner, s.Body)
}

// rangeKeyVal returns the key and value type produced by a range clause
// over an expression of type typ. If the range clause is not permitted
// the results are nil.
func rangeKeyVal(typ Type) (key, val Type) {
	switch typ := arrayPtrDeref(typ).(type) {
	case *Basic:
		if isString(typ) {
			return Typ[Int], universeRune // use 'rune' name
		}
	case *Array:
		return Typ[Int], typ.elem
	case *Slice:
		return Typ[Int], typ.elem
	case *Map:
		return typ.key, typ.elem
	case *Chan:
		return typ.elem, Typ[Invalid]
	}
	return
}
