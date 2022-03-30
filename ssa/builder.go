// Copyright 2013 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

// This file implements the BUILD phase of SSA construction.
//
// SSA construction has two phases, CREATE and BUILD.  In the CREATE phase
// (create.go), all packages are constructed and type-checked and
// definitions of all package members are created, method-sets are
// computed, and wrapper methods are synthesized.
// ssa.Packages are created in arbitrary order.
//
// In the BUILD phase (builder.go), the builder traverses the AST of
// each Go source function and generates SSA instructions for the
// function body.  Initializer expressions for package-level variables
// are emitted to the package's init() function in the order specified
// by github.com/mdempsky/amigo/types.Info.InitOrder, then code for each function in the
// package is generated in lexical order.
// The BUILD phases for distinct packages are independent and are
// executed in parallel.
//
// TODO(adonovan): indeed, building functions is now embarrassingly parallel.
// Audit for concurrency then benchmark using more goroutines.
//
// The builder's and Program's indices (maps) are populated and
// mutated during the CREATE phase, but during the BUILD phase they
// remain constant.  The sole exception is Prog.methodSets and its
// related maps, which are protected by a dedicated mutex.

import (
	"fmt"
	"go/constant"
	"go/token"
	"os"
	"sync"

	"github.com/mdempsky/amigo/syntax"
	"github.com/mdempsky/amigo/types"
)

type opaqueType struct {
	types.Type
	name string
}

func (t *opaqueType) String() string { return t.name }

var (
	varOk    = newVar("ok", tBool)
	varIndex = newVar("index", tInt)

	// Type constants.
	tBool       = types.Typ[types.Bool]
	tByte       = types.Typ[types.Byte]
	tInt        = types.Typ[types.Int]
	tInvalid    = types.Typ[types.Invalid]
	tString     = types.Typ[types.String]
	tUntypedNil = types.Typ[types.UntypedNil]
	tRangeIter  = &opaqueType{nil, "iter"} // the type of all "range" iterators
	tEface      = types.NewInterfaceType(nil, nil)

	// SSA Value constants.
	vZero = intConst(0)
	vOne  = intConst(1)
	vTrue = NewSSAConst(constant.MakeBool(true), tBool)
)

// builder holds state associated with the package currently being built.
// Its methods contain all the logic for AST-to-SSA conversion.
type builder struct{}

// cond emits to fn code to evaluate boolean condition e and jump
// to t or f depending on its value, performing various simplifications.
//
// Postcondition: fn.currentBlock is nil.
//
func (b *builder) cond(fn *Function, e syntax.Expr, t, f *BasicBlock) {
	switch e := e.(type) {
	case *syntax.ParenExpr:
		b.cond(fn, e.X, t, f)
		return

	case *syntax.Operation:
		if e.Y != nil { // BinaryExpr
			switch e.Op {
			case syntax.AndAnd:
				ltrue := fn.newBasicBlock("cond.true")
				b.cond(fn, e.X, ltrue, f)
				fn.currentBlock = ltrue
				b.cond(fn, e.Y, t, f)
				return

			case syntax.OrOr:
				lfalse := fn.newBasicBlock("cond.false")
				b.cond(fn, e.X, t, lfalse)
				fn.currentBlock = lfalse
				b.cond(fn, e.Y, t, f)
				return
			}
		} else { // UnaryExpr
			if e.Op == syntax.Not {
				b.cond(fn, e.X, f, t)
				return
			}
		}
	}

	// A traditional compiler would simplify "if false" (etc) here
	// but we do not, for better fidelity to the source code.
	//
	// The value of a constant condition may be platform-specific,
	// and may cause blocks that are reachable in some configuration
	// to be hidden from subsequent analyses such as bug-finding tools.
	emitIf(fn, b.expr(fn, e), t, f)
}

// logicalBinop emits code to fn to evaluate e, a &&- or
// ||-expression whose reified boolean value is wanted.
// The value is returned.
//
func (b *builder) logicalBinop(fn *Function, e *syntax.Operation) Value {
	rhs := fn.newBasicBlock("binop.rhs")
	done := fn.newBasicBlock("binop.done")

	// T(e) = T(e.X) = T(e.Y) after untyped constants have been
	// eliminated.
	// TODO(adonovan): not true; MyBool==MyBool yields UntypedBool.
	t := fn.Pkg.typeOf(e)

	var short Value // value of the short-circuit path
	switch e.Op {
	case syntax.AndAnd:
		b.cond(fn, e.X, rhs, done)
		short = NewSSAConst(constant.MakeBool(false), t)

	case syntax.OrOr:
		b.cond(fn, e.X, done, rhs)
		short = NewSSAConst(constant.MakeBool(true), t)
	}

	// Is rhs unreachable?
	if rhs.Preds == nil {
		// Simplify false&&y to false, true||y to true.
		fn.currentBlock = done
		return short
	}

	// Is done unreachable?
	if done.Preds == nil {
		// Simplify true&&y (or false||y) to y.
		fn.currentBlock = rhs
		return b.expr(fn, e.Y)
	}

	// All edges from e.X to done carry the short-circuit value.
	var edges []Value
	for range done.Preds {
		edges = append(edges, short)
	}

	// The edge from e.Y to done carries the value of e.Y.
	fn.currentBlock = rhs
	edges = append(edges, b.expr(fn, e.Y))
	emitJump(fn, done)
	fn.currentBlock = done

	phi := &Phi{Edges: edges, Comment: e.Op.String()}
	phi.pos = e.Pos() // OpPos
	phi.typ = t
	return done.emit(phi)
}

// exprN lowers a multi-result expression e to SSA form, emitting code
// to fn and returning a single Value whose type is a *types.Tuple.
// The caller must access the components via Extract.
//
// Multi-result expressions include CallExprs in a multi-value
// assignment or return statement, and "value,ok" uses of
// TypeAssertExpr, IndexExpr (when X is a map), and UnaryExpr (when Op
// is token.ARROW).
//
func (b *builder) exprN(fn *Function, e syntax.Expr) Value {
	typ := fn.Pkg.typeOf(e).(*types.Tuple)
	switch e := e.(type) {
	case *syntax.ParenExpr:
		return b.exprN(fn, e.X)

	case *syntax.CallExpr:
		// Currently, no built-in function nor type conversion
		// has multiple results, so we can avoid some of the
		// cases for single-valued CallExpr.
		var c Call
		b.setCall(fn, e, &c.Call)
		c.typ = typ
		return fn.emit(&c)

	case *syntax.IndexExpr:
		mapt := fn.Pkg.typeOf(e.X).Underlying().(*types.Map)
		lookup := &Lookup{
			X:       b.expr(fn, e.X),
			Index:   emitConv(fn, b.expr(fn, e.Index), mapt.Key()),
			CommaOk: true,
		}
		lookup.setType(typ)
		lookup.setPos(e.Pos() /*Lbrack*/)
		return fn.emit(lookup)

	case *syntax.AssertExpr:
		return emitTypeTest(fn, b.expr(fn, e.X), typ.At(0).Type(), e.Pos() /*Lparen*/)

	case *syntax.Operation: // must be receive <-
		unop := &UnOp{
			Op:      syntax.Recv,
			X:       b.expr(fn, e.X),
			CommaOk: true,
		}
		unop.setType(typ)
		unop.setPos(e.Pos() /*OpPos*/)
		return fn.emit(unop)
	}
	panic(fmt.Sprintf("exprN(%T) in %s", e, fn))
}

// builtin emits to fn SSA instructions to implement a call to the
// built-in function obj with the specified arguments
// and return type.  It returns the value defined by the result.
//
// The result is nil if no special handling was required; in this case
// the caller should treat this like an ordinary library function
// call.
//
func (b *builder) builtin(fn *Function, obj *types.Builtin, args []syntax.Expr, typ types.Type, pos syntax.Pos) Value {
	switch obj.Name() {
	case "make":
		switch typ.Underlying().(type) {
		case *types.Slice:
			n := b.expr(fn, args[1])
			m := n
			if len(args) == 3 {
				m = b.expr(fn, args[2])
			}
			if m, ok := m.(*SSAConst); ok {
				// treat make([]T, n, m) as new([m]T)[:n]
				cap := m.Int64()
				at := types.NewArray(typ.Underlying().(*types.Slice).Elem(), cap)
				alloc := emitNew(fn, at, pos)
				alloc.Comment = "makeslice"
				v := &SSASlice{
					X:    alloc,
					High: n,
				}
				v.setPos(pos)
				v.setType(typ)
				return fn.emit(v)
			}
			v := &MakeSlice{
				Len: n,
				Cap: m,
			}
			v.setPos(pos)
			v.setType(typ)
			return fn.emit(v)

		case *types.Map:
			var res Value
			if len(args) == 2 {
				res = b.expr(fn, args[1])
			}
			v := &MakeMap{Reserve: res}
			v.setPos(pos)
			v.setType(typ)
			return fn.emit(v)

		case *types.Chan:
			var sz Value = vZero
			if len(args) == 2 {
				sz = b.expr(fn, args[1])
			}
			v := &MakeChan{Size: sz}
			v.setPos(pos)
			v.setType(typ)
			return fn.emit(v)
		}

	case "new":
		alloc := emitNew(fn, deref(typ), pos)
		alloc.Comment = "new"
		return alloc

	case "len", "cap":
		// Special case: len or cap of an array or *array is
		// based on the type, not the value which may be nil.
		// We must still evaluate the value, though.  (If it
		// was side-effect free, the whole call would have
		// been constant-folded.)
		t := deref(fn.Pkg.typeOf(args[0])).Underlying()
		if at, ok := t.(*types.Array); ok {
			b.expr(fn, args[0]) // for effects only
			return intConst(at.Len())
		}
		// Otherwise treat as normal.

	case "panic":
		fn.emit(&Panic{
			X:   emitConv(fn, b.expr(fn, args[0]), tEface),
			pos: pos,
		})
		fn.currentBlock = fn.newBasicBlock("unreachable")
		return vTrue // any non-nil Value will do
	}
	return nil // treat all others as a regular function call
}

// addr lowers a single-result addressable expression e to SSA form,
// emitting code to fn and returning the location (an lvalue) defined
// by the expression.
//
// If escaping is true, addr marks the base variable of the
// addressable expression e as being a potentially escaping pointer
// value.  For example, in this code:
//
//   a := A{
//     b: [1]B{B{c: 1}}
//   }
//   return &a.b[0].c
//
// the application of & causes a.b[0].c to have its address taken,
// which means that ultimately the local variable a must be
// heap-allocated.  This is a simple but very conservative escape
// analysis.
//
// Operations forming potentially escaping pointers include:
// - &x, including when implicit in method call or composite literals.
// - a[:] iff a is an array (not *array)
// - references to variables in lexically enclosing functions.
//
func (b *builder) addr(fn *Function, e syntax.Expr, escaping bool) lvalue {
	switch e := e.(type) {
	case *syntax.Name:
		if isBlankIdent(e) {
			return blank{}
		}
		obj := fn.Pkg.objectOf(e)
		v := fn.Prog.packageLevelValue(obj) // var (address)
		if v == nil {
			v = fn.lookup(obj, escaping)
		}
		return &address{addr: v, pos: e.Pos(), expr: e}

	case *syntax.CompositeLit:
		t := deref(fn.Pkg.typeOf(e))
		var v *Alloc
		if escaping {
			v = emitNew(fn, t, e.Pos() /*Lbrace*/)
		} else {
			v = fn.addLocal(t, e.Pos() /*Lbrace*/)
		}
		v.Comment = "complit"
		var sb storebuf
		b.compLit(fn, v, e, true, &sb)
		sb.emit(fn)
		return &address{addr: v, pos: e.Pos() /*Lbrace*/, expr: e}

	case *syntax.ParenExpr:
		return b.addr(fn, e.X, escaping)

	case *syntax.SelectorExpr:
		sel, ok := fn.Pkg.info.Selections[e]
		if !ok {
			// qualified identifier
			return b.addr(fn, e.Sel, escaping)
		}
		if sel.Kind() != types.FieldVal {
			panic(sel)
		}
		wantAddr := true
		v := b.receiver(fn, e.X, wantAddr, escaping, sel)
		last := len(sel.Index()) - 1
		return &address{
			addr: emitFieldSelection(fn, v, sel.Index()[last], true, e.Sel),
			pos:  e.Sel.Pos(),
			expr: e.Sel,
		}

	case *syntax.IndexExpr:
		var x Value
		var et types.Type
		switch t := fn.Pkg.typeOf(e.X).Underlying().(type) {
		case *types.Array:
			x = b.addr(fn, e.X, escaping).address(fn)
			et = types.NewPointer(t.Elem())
		case *types.Pointer: // *array
			x = b.expr(fn, e.X)
			et = types.NewPointer(t.Elem().Underlying().(*types.Array).Elem())
		case *types.Slice:
			x = b.expr(fn, e.X)
			et = types.NewPointer(t.Elem())
		case *types.Map:
			return &element{
				m:   b.expr(fn, e.X),
				k:   emitConv(fn, b.expr(fn, e.Index), t.Key()),
				t:   t.Elem(),
				pos: e.Pos(), /*Lbrack*/
			}
		default:
			panic("unexpected container type in IndexExpr: " + t.String())
		}
		v := &IndexAddr{
			X:     x,
			Index: emitConv(fn, b.expr(fn, e.Index), tInt),
		}
		v.setPos(e.Pos() /*Lbrack*/)
		v.setType(et)
		return &address{addr: fn.emit(v), pos: e.Pos() /*Lbrack*/, expr: e}

	case *syntax.Operation: // was *syntax.StarExpr
		return &address{addr: b.expr(fn, e.X), pos: e.Pos() /*Star*/, expr: e}
	}

	panic(fmt.Sprintf("unexpected address expression: %T", e))
}

type store struct {
	lhs lvalue
	rhs Value
}

type storebuf struct{ stores []store }

func (sb *storebuf) store(lhs lvalue, rhs Value) {
	sb.stores = append(sb.stores, store{lhs, rhs})
}

func (sb *storebuf) emit(fn *Function) {
	for _, s := range sb.stores {
		s.lhs.store(fn, s.rhs)
	}
}

// assign emits to fn code to initialize the lvalue loc with the value
// of expression e.  If isZero is true, assign assumes that loc holds
// the zero value for its type.
//
// This is equivalent to loc.store(fn, b.expr(fn, e)), but may generate
// better code in some cases, e.g., for composite literals in an
// addressable location.
//
// If sb is not nil, assign generates code to evaluate expression e, but
// not to update loc.  Instead, the necessary stores are appended to the
// storebuf sb so that they can be executed later.  This allows correct
// in-place update of existing variables when the RHS is a composite
// literal that may reference parts of the LHS.
//
func (b *builder) assign(fn *Function, loc lvalue, e syntax.Expr, isZero bool, sb *storebuf) {
	// Can we initialize it in place?
	if e, ok := syntax.Unparen(e).(*syntax.CompositeLit); ok {
		// A CompositeLit never evaluates to a pointer,
		// so if the type of the location is a pointer,
		// an &-operation is implied.
		if _, ok := loc.(blank); !ok { // avoid calling blank.typ()
			if isPointer(loc.typ()) {
				ptr := b.addr(fn, e, true).address(fn)
				// copy address
				if sb != nil {
					sb.store(loc, ptr)
				} else {
					loc.store(fn, ptr)
				}
				return
			}
		}

		if _, ok := loc.(*address); ok {
			if isInterface(loc.typ()) {
				// e.g. var x interface{} = T{...}
				// Can't in-place initialize an interface value.
				// Fall back to copying.
			} else {
				// x = T{...} or x := T{...}
				addr := loc.address(fn)
				if sb != nil {
					b.compLit(fn, addr, e, isZero, sb)
				} else {
					var sb storebuf
					b.compLit(fn, addr, e, isZero, &sb)
					sb.emit(fn)
				}

				// Subtle: emit debug ref for aggregate types only;
				// slice and map are handled by store ops in compLit.
				switch loc.typ().Underlying().(type) {
				case *types.Struct, *types.Array:
					emitDebugRef(fn, e, addr, true)
				}

				return
			}
		}
	}

	// simple case: just copy
	rhs := b.expr(fn, e)
	if sb != nil {
		sb.store(loc, rhs)
	} else {
		loc.store(fn, rhs)
	}
}

// expr lowers a single-result expression e to SSA form, emitting code
// to fn and returning the Value defined by the expression.
//
func (b *builder) expr(fn *Function, e syntax.Expr) Value {
	e = syntax.Unparen(e)

	tv := fn.Pkg.info.Types[e]

	// Is expression a constant?
	if tv.Value != nil {
		return NewSSAConst(tv.Value, tv.Type)
	}

	var v Value
	if tv.Addressable() {
		// Prefer pointer arithmetic ({Index,Field}Addr) followed
		// by Load over subelement extraction (e.g. Index, Field),
		// to avoid large copies.
		v = b.addr(fn, e, false).load(fn)
	} else {
		v = b.expr0(fn, e, tv)
	}
	if fn.debugInfo() {
		emitDebugRef(fn, e, v, false)
	}
	return v
}

func (b *builder) expr0(fn *Function, e syntax.Expr, tv types.TypeAndValue) Value {
	switch e := e.(type) {
	case *syntax.BasicLit:
		panic("non-constant BasicLit") // unreachable

	case *syntax.FuncLit:
		fn2 := &Function{
			name:      fmt.Sprintf("%s$%d", fn.Name(), 1+len(fn.AnonFuncs)),
			Signature: fn.Pkg.typeOf(e.Type).Underlying().(*types.Signature),
			pos:       e.Type.Pos(), /*Func*/
			parent:    fn,
			Pkg:       fn.Pkg,
			Prog:      fn.Prog,
			syntax:    e,
		}
		fn.AnonFuncs = append(fn.AnonFuncs, fn2)
		b.buildFunction(fn2)
		if fn2.FreeVars == nil {
			return fn2
		}
		v := &MakeClosure{Fn: fn2}
		v.setType(tv.Type)
		for _, fv := range fn2.FreeVars {
			v.Bindings = append(v.Bindings, fv.outer)
			fv.outer = nil
		}
		return fn.emit(v)

	case *syntax.AssertExpr: // single-result form only
		return emitTypeAssert(fn, b.expr(fn, e.X), tv.Type, e.Pos() /*Lparen*/)

	case *syntax.CallExpr:
		if fn.Pkg.info.Types[e.Fun].IsType() {
			// Explicit type conversion, e.g. string(x) or big.Int(x)
			x := b.expr(fn, e.ArgList[0])
			y := emitConv(fn, x, tv.Type)
			if y != x {
				switch y := y.(type) {
				case *Convert:
					y.pos = e.Pos() /*Lparen*/
				case *ChangeType:
					y.pos = e.Pos() /*Lparen*/
				case *MakeInterface:
					y.pos = e.Pos() /*Lparen*/
				case *SliceToArrayPointer:
					y.pos = e.Pos() /*Lparen*/
				}
			}
			return y
		}
		// Call to "intrinsic" built-ins, e.g. new, make, panic.
		if id, ok := syntax.Unparen(e.Fun).(*syntax.Name); ok {
			if obj, ok := fn.Pkg.info.Uses[id].(*types.Builtin); ok {
				if v := b.builtin(fn, obj, e.ArgList, tv.Type, e.Pos() /*Lparen*/); v != nil {
					return v
				}
			}
		}
		// Regular function call.
		var v Call
		b.setCall(fn, e, &v.Call)
		v.setType(tv.Type)
		return fn.emit(&v)

	case *syntax.Operation:
		if e.Y == nil { // UnaryExpr
			switch e.Op {
			case syntax.And: // &X --- potentially escaping.
				addr := b.addr(fn, e.X, true)
				if x, ok := syntax.Unparen(e.X).(*syntax.Operation); ok && x.Op == syntax.Mul {
					// &*p must panic if p is nil (http://golang.org/s/go12nil).
					// For simplicity, we'll just (suboptimally) rely
					// on the side effects of a load.
					// TODO(adonovan): emit dedicated nilcheck.
					addr.load(fn)
				}
				return addr.address(fn)
			case syntax.Add:
				return b.expr(fn, e.X)
			case syntax.Not, syntax.Recv, syntax.Sub, syntax.Xor:
				v := &UnOp{
					Op: e.Op,
					X:  b.expr(fn, e.X),
				}
				v.setPos(e.Pos() /*OpPos*/)
				v.setType(tv.Type)
				return fn.emit(v)
			case syntax.Mul:
				// Addressable types (lvalues)
				return b.addr(fn, e, false).load(fn)
			default:
				panic(e.Op)
			}
		} else { // BinaryExpr
			switch e.Op {
			case syntax.AndAnd, syntax.OrOr:
				return b.logicalBinop(fn, e)
			case syntax.Shl, syntax.Shr:
				fallthrough
			case syntax.Add, syntax.Sub, syntax.Mul, syntax.Div, syntax.Rem, syntax.And, syntax.Or, syntax.Xor, syntax.AndNot:
				return emitArith(fn, e.Op, b.expr(fn, e.X), b.expr(fn, e.Y), tv.Type, e.Pos() /*OpPos*/)

			case syntax.Eql, syntax.Neq, syntax.Gtr, syntax.Lss, syntax.Leq, syntax.Geq:
				cmp := emitCompare(fn, e.Op, b.expr(fn, e.X), b.expr(fn, e.Y), e.Pos() /*OpPos*/)
				// The type of x==y may be UntypedBool.
				return emitConv(fn, cmp, types.Default(tv.Type))
			default:
				panic("illegal op in BinaryExpr: " + e.Op.String())
			}
		}

	case *syntax.SliceExpr:
		var low, high, max Value
		var x Value
		switch fn.Pkg.typeOf(e.X).Underlying().(type) {
		case *types.Array:
			// Potentially escaping.
			x = b.addr(fn, e.X, true).address(fn)
		case *types.Basic, *types.Slice, *types.Pointer: // *array
			x = b.expr(fn, e.X)
		default:
			panic("unreachable")
		}
		// TODO(mdempsky): Why do we evaluate high before low?
		if e.Index[1] != nil {
			high = b.expr(fn, e.Index[1])
		}
		if e.Index[0] != nil {
			low = b.expr(fn, e.Index[0])
		}
		if e.Index[2] != nil {
			max = b.expr(fn, e.Index[2])
		}
		v := &SSASlice{
			X:    x,
			Low:  low,
			High: high,
			Max:  max,
		}
		v.setPos(e.Pos() /*Lbrack*/)
		v.setType(tv.Type)
		return fn.emit(v)

	case *syntax.Name:
		obj := fn.Pkg.info.Uses[e]
		// Universal built-in or nil?
		switch obj := obj.(type) {
		case *types.Builtin:
			return &SSABuiltin{name: obj.Name(), sig: tv.Type.(*types.Signature)}
		case *types.Nil:
			return nilConst(tv.Type)
		}
		// Package-level func or var?
		if v := fn.Prog.packageLevelValue(obj); v != nil {
			if _, ok := obj.(*types.Var); ok {
				return emitLoad(fn, v) // var (address)
			}
			return v // (func)
		}
		// Local var.
		return emitLoad(fn, fn.lookup(obj, false)) // var (address)

	case *syntax.SelectorExpr:
		sel, ok := fn.Pkg.info.Selections[e]
		if !ok {
			// builtin unsafe.{Add,Slice}
			if obj, ok := fn.Pkg.info.Uses[e.Sel].(*types.Builtin); ok {
				return &SSABuiltin{name: obj.Name(), sig: tv.Type.(*types.Signature)}
			}
			// qualified identifier
			return b.expr(fn, e.Sel)
		}
		switch sel.Kind() {
		case types.MethodExpr:
			// (*T).f or T.f, the method f from the method-set of type T.
			// The result is a "thunk".
			return emitConv(fn, makeThunk(fn.Prog, sel), tv.Type)

		case types.MethodVal:
			// e.f where e is an expression and f is a method.
			// The result is a "bound".
			obj := sel.Obj().(*types.Func)
			rt := recvType(obj)
			wantAddr := isPointer(rt)
			escaping := true
			v := b.receiver(fn, e.X, wantAddr, escaping, sel)
			if isInterface(rt) {
				// If v has interface type I,
				// we must emit a check that v is non-nil.
				// We use: typeassert v.(I).
				emitTypeAssert(fn, v, rt, syntax.NoPos)
			}
			c := &MakeClosure{
				Fn:       makeBound(fn.Prog, obj),
				Bindings: []Value{v},
			}
			c.setPos(e.Sel.Pos())
			c.setType(tv.Type)
			return fn.emit(c)

		case types.FieldVal:
			indices := sel.Index()
			last := len(indices) - 1
			v := b.expr(fn, e.X)
			v = emitImplicitSelections(fn, v, indices[:last])
			v = emitFieldSelection(fn, v, indices[last], false, e.Sel)
			return v
		}

		panic("unexpected expression-relative selector")

	case *syntax.IndexExpr:
		switch t := fn.Pkg.typeOf(e.X).Underlying().(type) {
		case *types.Array:
			// Non-addressable array (in a register).
			v := &Index{
				X:     b.expr(fn, e.X),
				Index: emitConv(fn, b.expr(fn, e.Index), tInt),
			}
			v.setPos(e.Pos() /*Lbrack*/)
			v.setType(t.Elem())
			return fn.emit(v)

		case *types.Map:
			// Maps are not addressable.
			mapt := fn.Pkg.typeOf(e.X).Underlying().(*types.Map)
			v := &Lookup{
				X:     b.expr(fn, e.X),
				Index: emitConv(fn, b.expr(fn, e.Index), mapt.Key()),
			}
			v.setPos(e.Pos() /*Lbrack*/)
			v.setType(mapt.Elem())
			return fn.emit(v)

		case *types.Basic: // => string
			// Strings are not addressable.
			v := &Lookup{
				X:     b.expr(fn, e.X),
				Index: b.expr(fn, e.Index),
			}
			v.setPos(e.Pos() /*Lbrack*/)
			v.setType(tByte)
			return fn.emit(v)

		case *types.Slice, *types.Pointer: // *array
			// Addressable slice/array; use IndexAddr and Load.
			return b.addr(fn, e, false).load(fn)

		default:
			panic("unexpected container type in IndexExpr: " + t.String())
		}

	case *syntax.CompositeLit:
		// Addressable types (lvalues)
		return b.addr(fn, e, false).load(fn)
	}

	panic(fmt.Sprintf("unexpected expr: %T", e))
}

// stmtList emits to fn code for all statements in list.
func (b *builder) stmtList(fn *Function, list []syntax.Stmt) {
	for _, s := range list {
		b.stmt(fn, s)
	}
}

// receiver emits to fn code for expression e in the "receiver"
// position of selection e.f (where f may be a field or a method) and
// returns the effective receiver after applying the implicit field
// selections of sel.
//
// wantAddr requests that the result is an an address.  If
// !sel.Indirect(), this may require that e be built in addr() mode; it
// must thus be addressable.
//
// escaping is defined as per builder.addr().
//
func (b *builder) receiver(fn *Function, e syntax.Expr, wantAddr, escaping bool, sel *types.Selection) Value {
	var v Value
	if wantAddr && !sel.Indirect() && !isPointer(fn.Pkg.typeOf(e)) {
		v = b.addr(fn, e, escaping).address(fn)
	} else {
		v = b.expr(fn, e)
	}

	last := len(sel.Index()) - 1
	v = emitImplicitSelections(fn, v, sel.Index()[:last])
	if !wantAddr && isPointer(v.Type()) {
		v = emitLoad(fn, v)
	}
	return v
}

// setCallFunc populates the function parts of a CallCommon structure
// (Func, Method, Recv, Args[0]) based on the kind of invocation
// occurring in e.
//
func (b *builder) setCallFunc(fn *Function, e *syntax.CallExpr, c *CallCommon) {
	c.pos = e.Pos() /*Lparen*/

	// Is this a method call?
	if selector, ok := syntax.Unparen(e.Fun).(*syntax.SelectorExpr); ok {
		sel, ok := fn.Pkg.info.Selections[selector]
		if ok && sel.Kind() == types.MethodVal {
			obj := sel.Obj().(*types.Func)
			recv := recvType(obj)
			wantAddr := isPointer(recv)
			escaping := true
			v := b.receiver(fn, selector.X, wantAddr, escaping, sel)
			if isInterface(recv) {
				// Invoke-mode call.
				c.Value = v
				c.Method = obj
			} else {
				// "Call"-mode call.
				c.Value = fn.Prog.declaredFunc(obj)
				c.Args = append(c.Args, v)
			}
			return
		}

		// sel.Kind()==MethodExpr indicates T.f() or (*T).f():
		// a statically dispatched call to the method f in the
		// method-set of T or *T.  T may be an interface.
		//
		// e.Fun would evaluate to a concrete method, interface
		// wrapper function, or promotion wrapper.
		//
		// For now, we evaluate it in the usual way.
		//
		// TODO(adonovan): opt: inline expr() here, to make the
		// call static and to avoid generation of wrappers.
		// It's somewhat tricky as it may consume the first
		// actual parameter if the call is "invoke" mode.
		//
		// Examples:
		//  type T struct{}; func (T) f() {}   // "call" mode
		//  type T interface { f() }           // "invoke" mode
		//
		//  type S struct{ T }
		//
		//  var s S
		//  S.f(s)
		//  (*S).f(&s)
		//
		// Suggested approach:
		// - consume the first actual parameter expression
		//   and build it with b.expr().
		// - apply implicit field selections.
		// - use MethodVal logic to populate fields of c.
	}

	// Evaluate the function operand in the usual way.
	c.Value = b.expr(fn, e.Fun)
}

// emitCallArgs emits to f code for the actual parameters of call e to
// a (possibly built-in) function of effective type sig.
// The argument values are appended to args, which is then returned.
//
func (b *builder) emitCallArgs(fn *Function, sig *types.Signature, e *syntax.CallExpr, args []Value) []Value {
	// f(x, y, z...): pass slice z straight through.
	if e.HasDots {
		for i, arg := range e.ArgList {
			v := emitConv(fn, b.expr(fn, arg), sig.Params().At(i).Type())
			args = append(args, v)
		}
		return args
	}

	offset := len(args) // 1 if call has receiver, 0 otherwise

	// Evaluate actual parameter expressions.
	//
	// If this is a chained call of the form f(g()) where g has
	// multiple return values (MRV), they are flattened out into
	// args; a suffix of them may end up in a varargs slice.
	for _, arg := range e.ArgList {
		v := b.expr(fn, arg)
		if ttuple, ok := v.Type().(*types.Tuple); ok { // MRV chain
			for i, n := 0, ttuple.Len(); i < n; i++ {
				args = append(args, emitExtract(fn, v, i))
			}
		} else {
			args = append(args, v)
		}
	}

	// Actual->formal assignability conversions for normal parameters.
	np := sig.Params().Len() // number of normal parameters
	if sig.Variadic() {
		np--
	}
	for i := 0; i < np; i++ {
		args[offset+i] = emitConv(fn, args[offset+i], sig.Params().At(i).Type())
	}

	// Actual->formal assignability conversions for variadic parameter,
	// and construction of slice.
	if sig.Variadic() {
		varargs := args[offset+np:]
		st := sig.Params().At(np).Type().(*types.Slice)
		vt := st.Elem()
		if len(varargs) == 0 {
			args = append(args, nilConst(st))
		} else {
			// Replace a suffix of args with a slice containing it.
			at := types.NewArray(vt, int64(len(varargs)))
			a := emitNew(fn, at, syntax.NoPos)
			a.setPos(e.Pos() /*Rparen*/)
			a.Comment = "varargs"
			for i, arg := range varargs {
				iaddr := &IndexAddr{
					X:     a,
					Index: intConst(int64(i)),
				}
				iaddr.setType(types.NewPointer(vt))
				fn.emit(iaddr)
				emitStore(fn, iaddr, arg, arg.Pos())
			}
			s := &SSASlice{X: a}
			s.setType(st)
			args[offset+np] = fn.emit(s)
			args = args[:offset+np+1]
		}
	}
	return args
}

// setCall emits to fn code to evaluate all the parameters of a function
// call e, and populates *c with those values.
//
func (b *builder) setCall(fn *Function, e *syntax.CallExpr, c *CallCommon) {
	// First deal with the f(...) part and optional receiver.
	b.setCallFunc(fn, e, c)

	// Then append the other actual parameters.
	sig, _ := fn.Pkg.typeOf(e.Fun).Underlying().(*types.Signature)
	if sig == nil {
		panic(fmt.Sprintf("no signature for call of %s", e.Fun))
	}
	c.Args = b.emitCallArgs(fn, sig, e, c.Args)
}

// assignOp emits to fn code to perform loc <op>= val.
func (b *builder) assignOp(fn *Function, loc lvalue, val Value, op syntax.Operator, pos syntax.Pos) {
	oldv := loc.load(fn)
	loc.store(fn, emitArith(fn, op, oldv, emitConv(fn, val, oldv.Type()), loc.typ(), pos))
}

// localValueSpec emits to fn code to define all of the vars in the
// function-local ValueSpec, spec.
//
func (b *builder) localValueSpec(fn *Function, spec *syntax.VarSpec) {
	values := unpackExprList(spec.Values)

	switch {
	case len(values) == len(spec.NameList):
		// e.g. var x, y = 0, 1
		// 1:1 assignment
		for i, id := range spec.NameList {
			if !isBlankIdent(id) {
				fn.addLocalForIdent(id)
			}
			lval := b.addr(fn, id, false) // non-escaping
			b.assign(fn, lval, values[i], true, nil)
		}

	case len(values) == 0:
		// e.g. var x, y int
		// Locals are implicitly zero-initialized.
		for _, id := range spec.NameList {
			if !isBlankIdent(id) {
				lhs := fn.addLocalForIdent(id)
				if fn.debugInfo() {
					emitDebugRef(fn, id, lhs, true)
				}
			}
		}

	default:
		// e.g. var x, y = pos()
		tuple := b.exprN(fn, values[0])
		for i, id := range spec.NameList {
			if !isBlankIdent(id) {
				fn.addLocalForIdent(id)
				lhs := b.addr(fn, id, false) // non-escaping
				lhs.store(fn, emitExtract(fn, tuple, i))
			}
		}
	}
}

// assignStmt emits code to fn for a parallel assignment of rhss to lhss.
// isDef is true if this is a short variable declaration (:=).
//
// Note the similarity with localValueSpec.
//
func (b *builder) assignStmt(fn *Function, lhss, rhss []syntax.Expr, isDef bool) {
	// Side effects of all LHSs and RHSs must occur in left-to-right order.
	lvals := make([]lvalue, len(lhss))
	isZero := make([]bool, len(lhss))
	for i, lhs := range lhss {
		var lval lvalue = blank{}
		if !isBlankIdent(lhs) {
			if isDef {
				if obj := fn.Pkg.info.Defs[lhs.(*syntax.Name)]; obj != nil {
					fn.addNamedLocal(obj)
					isZero[i] = true
				}
			}
			lval = b.addr(fn, lhs, false) // non-escaping
		}
		lvals[i] = lval
	}
	if len(lhss) == len(rhss) {
		// Simple assignment:   x     = f()        (!isDef)
		// Parallel assignment: x, y  = f(), g()   (!isDef)
		// or short var decl:   x, y := f(), g()   (isDef)
		//
		// In all cases, the RHSs may refer to the LHSs,
		// so we need a storebuf.
		var sb storebuf
		for i := range rhss {
			b.assign(fn, lvals[i], rhss[i], isZero[i], &sb)
		}
		sb.emit(fn)
	} else {
		// e.g. x, y = pos()
		tuple := b.exprN(fn, rhss[0])
		emitDebugRef(fn, rhss[0], tuple, false)
		for i, lval := range lvals {
			lval.store(fn, emitExtract(fn, tuple, i))
		}
	}
}

// arrayLen returns the length of the array whose composite literal elements are elts.
func (b *builder) arrayLen(fn *Function, elts []syntax.Expr) int64 {
	var max int64 = -1
	var i int64 = -1
	for _, e := range elts {
		if kv, ok := e.(*syntax.KeyValueExpr); ok {
			i = b.expr(fn, kv.Key).(*SSAConst).Int64()
		} else {
			i++
		}
		if i > max {
			max = i
		}
	}
	return max + 1
}

// compLit emits to fn code to initialize a composite literal e at
// address addr with type typ.
//
// Nested composite literals are recursively initialized in place
// where possible. If isZero is true, compLit assumes that addr
// holds the zero value for typ.
//
// Because the elements of a composite literal may refer to the
// variables being updated, as in the second line below,
//	x := T{a: 1}
//	x = T{a: x.a}
// all the reads must occur before all the writes.  Thus all stores to
// loc are emitted to the storebuf sb for later execution.
//
// A CompositeLit may have pointer type only in the recursive (nested)
// case when the type name is implicit.  e.g. in []*T{{}}, the inner
// literal has type *T behaves like &T{}.
// In that case, addr must hold a T, not a *T.
//
func (b *builder) compLit(fn *Function, addr Value, e *syntax.CompositeLit, isZero bool, sb *storebuf) {
	typ := deref(fn.Pkg.typeOf(e))
	switch t := typ.Underlying().(type) {
	case *types.Struct:
		if !isZero && len(e.ElemList) != t.NumFields() {
			// memclear
			sb.store(&address{addr, e.Pos() /*Lbrace*/, nil},
				zeroValue(fn, deref(addr.Type())))
			isZero = true
		}
		for i, e := range e.ElemList {
			fieldIndex := i
			pos := e.Pos()
			if kv, ok := e.(*syntax.KeyValueExpr); ok {
				fname := kv.Key.(*syntax.Name).Value
				for i, n := 0, t.NumFields(); i < n; i++ {
					sf := t.Field(i)
					if sf.Name() == fname {
						fieldIndex = i
						pos = kv.Pos() /*Colon*/
						e = kv.Value
						break
					}
				}
			}
			sf := t.Field(fieldIndex)
			faddr := &FieldAddr{
				X:     addr,
				Field: fieldIndex,
			}
			faddr.setType(types.NewPointer(sf.Type()))
			fn.emit(faddr)
			b.assign(fn, &address{addr: faddr, pos: pos, expr: e}, e, isZero, sb)
		}

	case *types.Array, *types.Slice:
		var at *types.Array
		var array Value
		switch t := t.(type) {
		case *types.Slice:
			at = types.NewArray(t.Elem(), b.arrayLen(fn, e.ElemList))
			alloc := emitNew(fn, at, e.Pos() /*Lbrace*/)
			alloc.Comment = "slicelit"
			array = alloc
		case *types.Array:
			at = t
			array = addr

			if !isZero && int64(len(e.ElemList)) != at.Len() {
				// memclear
				sb.store(&address{array, e.Pos() /*Lbrace*/, nil},
					zeroValue(fn, deref(array.Type())))
			}
		}

		var idx *SSAConst
		for _, e := range e.ElemList {
			pos := e.Pos()
			if kv, ok := e.(*syntax.KeyValueExpr); ok {
				idx = b.expr(fn, kv.Key).(*SSAConst)
				pos = kv.Pos() /*Colon*/
				e = kv.Value
			} else {
				var idxval int64
				if idx != nil {
					idxval = idx.Int64() + 1
				}
				idx = intConst(idxval)
			}
			iaddr := &IndexAddr{
				X:     array,
				Index: idx,
			}
			iaddr.setType(types.NewPointer(at.Elem()))
			fn.emit(iaddr)
			if t != at { // slice
				// backing array is unaliased => storebuf not needed.
				b.assign(fn, &address{addr: iaddr, pos: pos, expr: e}, e, true, nil)
			} else {
				b.assign(fn, &address{addr: iaddr, pos: pos, expr: e}, e, true, sb)
			}
		}

		if t != at { // slice
			s := &SSASlice{X: array}
			s.setPos(e.Pos() /*Lbrace*/)
			s.setType(typ)
			sb.store(&address{addr: addr, pos: e.Pos() /*Lbrace*/, expr: e}, fn.emit(s))
		}

	case *types.Map:
		m := &MakeMap{Reserve: intConst(int64(len(e.ElemList)))}
		m.setPos(e.Pos() /*Lbrace*/)
		m.setType(typ)
		fn.emit(m)
		for _, e := range e.ElemList {
			e := e.(*syntax.KeyValueExpr)

			// If a key expression in a map literal is itself a
			// composite literal, the type may be omitted.
			// For example:
			//	map[*struct{}]bool{{}: true}
			// An &-operation may be implied:
			//	map[*struct{}]bool{&struct{}{}: true}
			var key Value
			if _, ok := syntax.Unparen(e.Key).(*syntax.CompositeLit); ok && isPointer(t.Key()) {
				// A CompositeLit never evaluates to a pointer,
				// so if the type of the location is a pointer,
				// an &-operation is implied.
				key = b.addr(fn, e.Key, true).address(fn)
			} else {
				key = b.expr(fn, e.Key)
			}

			loc := element{
				m:   m,
				k:   emitConv(fn, key, t.Key()),
				t:   t.Elem(),
				pos: e.Pos(), /*Colon*/
			}

			// We call assign() only because it takes care
			// of any &-operation required in the recursive
			// case, e.g.,
			// map[int]*struct{}{0: {}} implies &struct{}{}.
			// In-place update is of course impossible,
			// and no storebuf is needed.
			b.assign(fn, &loc, e.Value, true, nil)
		}
		sb.store(&address{addr: addr, pos: e.Pos() /*Lbrace*/, expr: e}, m)

	default:
		panic("unexpected CompositeLit type: " + t.String())
	}
}

// switchStmt emits to fn code for the switch statement s, optionally
// labelled by label.
//
func (b *builder) switchStmt(fn *Function, s *syntax.SwitchStmt, label *lblock) {
	// We treat SwitchStmt like a sequential if-else chain.
	// Multiway dispatch can be recovered later by ssautil.Switches()
	// to those cases that are free of side effects.
	if s.Init != nil {
		b.stmt(fn, s.Init)
	}
	var tag Value = vTrue
	if s.Tag != nil {
		tag = b.expr(fn, s.Tag)
	}
	done := fn.newBasicBlock("switch.done")
	if label != nil {
		label._break = done
	}
	// We pull the default case (if present) down to the end.
	// But each fallthrough label must point to the next
	// body block in source order, so we preallocate a
	// body block (fallthru) for the next case.
	// Unfortunately this makes for a confusing block order.
	var dfltBody *[]syntax.Stmt
	var dfltFallthrough *BasicBlock
	var fallthru, dfltBlock *BasicBlock
	ncases := len(s.Body)
	for i, clause := range s.Body {
		body := fallthru
		if body == nil {
			body = fn.newBasicBlock("switch.body") // first case only
		}

		// Preallocate body block for the next case.
		fallthru = done
		if i+1 < ncases {
			fallthru = fn.newBasicBlock("switch.body")
		}

		cc := clause
		if cc.Cases == nil {
			// Default case.
			dfltBody = &cc.Body
			dfltFallthrough = fallthru
			dfltBlock = body
			continue
		}

		var nextCond *BasicBlock
		for _, cond := range unpackExprList(cc.Cases) {
			nextCond = fn.newBasicBlock("switch.next")
			// TODO(adonovan): opt: when tag==vTrue, we'd
			// get better code if we use b.cond(cond)
			// instead of BinOp(EQL, tag, b.expr(cond))
			// followed by If.  Don't forget conversions
			// though.
			cond := emitCompare(fn, syntax.Eql, tag, b.expr(fn, cond), syntax.NoPos)
			emitIf(fn, cond, body, nextCond)
			fn.currentBlock = nextCond
		}
		fn.currentBlock = body
		fn.targets = &targets{
			tail:         fn.targets,
			_break:       done,
			_fallthrough: fallthru,
		}
		b.stmtList(fn, cc.Body)
		fn.targets = fn.targets.tail
		emitJump(fn, done)
		fn.currentBlock = nextCond
	}
	if dfltBlock != nil {
		emitJump(fn, dfltBlock)
		fn.currentBlock = dfltBlock
		fn.targets = &targets{
			tail:         fn.targets,
			_break:       done,
			_fallthrough: dfltFallthrough,
		}
		b.stmtList(fn, *dfltBody)
		fn.targets = fn.targets.tail
	}
	emitJump(fn, done)
	fn.currentBlock = done
}

// typeSwitchStmt emits to fn code for the type switch statement s, optionally
// labelled by label.
//
func (b *builder) typeSwitchStmt(fn *Function, s *syntax.SwitchStmt, label *lblock) {
	guard := s.Tag.(*syntax.TypeSwitchGuard)

	// We treat TypeSwitchStmt like a sequential if-else chain.
	// Multiway dispatch can be recovered later by ssautil.Switches().

	// Typeswitch lowering:
	//
	// var x X
	// switch y := x.(type) {
	// case T1, T2: S1                  // >1 	(y := x)
	// case nil:    SN                  // nil 	(y := x)
	// default:     SD                  // 0 types 	(y := x)
	// case T3:     S3                  // 1 type 	(y := x.(T3))
	// }
	//
	//      ...s.Init...
	// 	x := eval x
	// .caseT1:
	// 	t1, ok1 := typeswitch,ok x <T1>
	// 	if ok1 then goto S1 else goto .caseT2
	// .caseT2:
	// 	t2, ok2 := typeswitch,ok x <T2>
	// 	if ok2 then goto S1 else goto .caseNil
	// .S1:
	//      y := x
	// 	...S1...
	// 	goto done
	// .caseNil:
	// 	if t2, ok2 := typeswitch,ok x <T2>
	// 	if x == nil then goto SN else goto .caseT3
	// .SN:
	//      y := x
	// 	...SN...
	// 	goto done
	// .caseT3:
	// 	t3, ok3 := typeswitch,ok x <T3>
	// 	if ok3 then goto S3 else goto default
	// .S3:
	//      y := t3
	// 	...S3...
	// 	goto done
	// .default:
	//      y := x
	// 	...SD...
	// 	goto done
	// .done:

	if s.Init != nil {
		b.stmt(fn, s.Init)
	}

	x := b.expr(fn, guard.X)

	done := fn.newBasicBlock("typeswitch.done")
	if label != nil {
		label._break = done
	}
	var default_ *syntax.CaseClause
	for _, clause := range s.Body {
		cc := clause
		if cc.Cases == nil {
			default_ = cc
			continue
		}
		body := fn.newBasicBlock("typeswitch.body")
		var next *BasicBlock
		var casetype types.Type
		var ti Value // ti, ok := typeassert,ok x <Ti>
		for _, cond := range unpackExprList(cc.Cases) {
			next = fn.newBasicBlock("typeswitch.next")
			casetype = fn.Pkg.typeOf(cond)
			var condv Value
			if casetype == tUntypedNil {
				condv = emitCompare(fn, syntax.Eql, x, nilConst(x.Type()), syntax.NoPos)
				ti = x
			} else {
				yok := emitTypeTest(fn, x, casetype, cc.Pos() /*Case*/)
				ti = emitExtract(fn, yok, 0)
				condv = emitExtract(fn, yok, 1)
			}
			emitIf(fn, condv, body, next)
			fn.currentBlock = next
		}
		if len(unpackExprList(cc.Cases)) != 1 {
			ti = x
		}
		fn.currentBlock = body
		b.typeCaseBody(fn, cc, ti, done)
		fn.currentBlock = next
	}
	if default_ != nil {
		b.typeCaseBody(fn, default_, x, done)
	} else {
		emitJump(fn, done)
	}
	fn.currentBlock = done
}

func (b *builder) typeCaseBody(fn *Function, cc *syntax.CaseClause, x Value, done *BasicBlock) {
	if obj := fn.Pkg.info.Implicits[cc]; obj != nil {
		// In a switch y := x.(type), each case clause
		// implicitly declares a distinct object y.
		// In a single-type case, y has that type.
		// In multi-type cases, 'case nil' and default,
		// y has the same type as the interface operand.
		emitStore(fn, fn.addNamedLocal(obj), x, obj.Pos())
	}
	fn.targets = &targets{
		tail:   fn.targets,
		_break: done,
	}
	b.stmtList(fn, cc.Body)
	fn.targets = fn.targets.tail
	emitJump(fn, done)
}

// selectStmt emits to fn code for the select statement s, optionally
// labelled by label.
//
func (b *builder) selectStmt(fn *Function, s *syntax.SelectStmt, label *lblock) {
	// A blocking select of a single case degenerates to a
	// simple send or receive.
	// TODO(adonovan): opt: is this optimization worth its weight?
	if len(s.Body) == 1 {
		clause := s.Body[0]
		if clause.Comm != nil {
			b.stmt(fn, clause.Comm)
			done := fn.newBasicBlock("select.done")
			if label != nil {
				label._break = done
			}
			fn.targets = &targets{
				tail:   fn.targets,
				_break: done,
			}
			b.stmtList(fn, clause.Body)
			fn.targets = fn.targets.tail
			emitJump(fn, done)
			fn.currentBlock = done
			return
		}
	}

	// First evaluate all channels in all cases, and find
	// the directions of each state.
	var states []*SelectState
	blocking := true
	debugInfo := fn.debugInfo()
	for _, clause := range s.Body {
		var st *SelectState
		switch comm := clause.Comm.(type) {
		case nil: // default case
			blocking = false
			continue

		case *syntax.SendStmt: // ch <- i
			ch := b.expr(fn, comm.Chan)
			st = &SelectState{
				Dir:  syntax.SendOnly,
				Chan: ch,
				Send: emitConv(fn, b.expr(fn, comm.Value),
					ch.Type().Underlying().(*types.Chan).Elem()),
				Pos: comm.Pos(), /*Arrow*/
			}
			if debugInfo {
				st.DebugNode = comm
			}

		case *syntax.AssignStmt: // x := <-ch
			recv := syntax.Unparen(comm.Rhs).(*syntax.Operation)
			st = &SelectState{
				Dir:  syntax.RecvOnly,
				Chan: b.expr(fn, recv.X),
				Pos:  recv.Pos(), /*OpPos*/
			}
			if debugInfo {
				st.DebugNode = recv
			}

		case *syntax.ExprStmt: // <-ch
			recv := syntax.Unparen(comm.X).(*syntax.Operation)
			st = &SelectState{
				Dir:  syntax.RecvOnly,
				Chan: b.expr(fn, recv.X),
				Pos:  recv.Pos(), /*OpPos*/
			}
			if debugInfo {
				st.DebugNode = recv
			}
		}
		states = append(states, st)
	}

	// We dispatch on the (fair) result of Select using a
	// sequential if-else chain, in effect:
	//
	// idx, recvOk, r0...r_n-1 := select(...)
	// if idx == 0 {  // receive on channel 0  (first receive => r0)
	//     x, ok := r0, recvOk
	//     ...state0...
	// } else if v == 1 {   // send on channel 1
	//     ...state1...
	// } else {
	//     ...default...
	// }
	sel := &Select{
		States:   states,
		Blocking: blocking,
	}
	sel.setPos(s.Pos() /*Select*/)
	var vars []*types.Var
	vars = append(vars, varIndex, varOk)
	for _, st := range states {
		if st.Dir == syntax.RecvOnly {
			tElem := st.Chan.Type().Underlying().(*types.Chan).Elem()
			vars = append(vars, anonVar(tElem))
		}
	}
	sel.setType(types.NewTuple(vars...))

	fn.emit(sel)
	idx := emitExtract(fn, sel, 0)

	done := fn.newBasicBlock("select.done")
	if label != nil {
		label._break = done
	}

	var defaultBody *[]syntax.Stmt
	state := 0
	r := 2 // index in 'sel' tuple of value; increments if st.Dir==RECV
	for _, cc := range s.Body {
		clause := cc
		if clause.Comm == nil {
			defaultBody = &clause.Body
			continue
		}
		body := fn.newBasicBlock("select.body")
		next := fn.newBasicBlock("select.next")
		emitIf(fn, emitCompare(fn, syntax.Eql, idx, intConst(int64(state)), syntax.NoPos), body, next)
		fn.currentBlock = body
		fn.targets = &targets{
			tail:   fn.targets,
			_break: done,
		}
		switch comm := clause.Comm.(type) {
		case *syntax.ExprStmt: // <-ch
			if debugInfo {
				v := emitExtract(fn, sel, r)
				emitDebugRef(fn, states[state].DebugNode.(syntax.Expr), v, false)
			}
			r++

		case *syntax.AssignStmt: // x := <-states[state].Chan
			lhs := unpackExprList(comm.Lhs)

			if comm.Op == syntax.Def {
				fn.addLocalForIdent(lhs[0].(*syntax.Name))
			}
			x := b.addr(fn, lhs[0], false) // non-escaping
			v := emitExtract(fn, sel, r)
			if debugInfo {
				emitDebugRef(fn, states[state].DebugNode.(syntax.Expr), v, false)
			}
			x.store(fn, v)

			if len(lhs) == 2 { // x, ok := ...
				if comm.Op == syntax.Def {
					fn.addLocalForIdent(lhs[1].(*syntax.Name))
				}
				ok := b.addr(fn, lhs[1], false) // non-escaping
				ok.store(fn, emitExtract(fn, sel, 1))
			}
			r++
		}
		b.stmtList(fn, clause.Body)
		fn.targets = fn.targets.tail
		emitJump(fn, done)
		fn.currentBlock = next
		state++
	}
	if defaultBody != nil {
		fn.targets = &targets{
			tail:   fn.targets,
			_break: done,
		}
		b.stmtList(fn, *defaultBody)
		fn.targets = fn.targets.tail
	} else {
		// A blocking select must match some case.
		// (This should really be a runtime.errorString, not a string.)
		fn.emit(&Panic{
			X: emitConv(fn, stringConst("blocking select matched no case"), tEface),
		})
		fn.currentBlock = fn.newBasicBlock("unreachable")
	}
	emitJump(fn, done)
	fn.currentBlock = done
}

// forStmt emits to fn code for the for statement s, optionally
// labelled by label.
//
func (b *builder) forStmt(fn *Function, s *syntax.ForStmt, label *lblock) {
	//	...init...
	//      jump loop
	// loop:
	//      if cond goto body else done
	// body:
	//      ...body...
	//      jump post
	// post:				 (target of continue)
	//      ...post...
	//      jump loop
	// done:                                 (target of break)
	if s.Init != nil {
		b.stmt(fn, s.Init)
	}
	body := fn.newBasicBlock("for.body")
	done := fn.newBasicBlock("for.done") // target of 'break'
	loop := body                         // target of back-edge
	if s.Cond != nil {
		loop = fn.newBasicBlock("for.loop")
	}
	cont := loop // target of 'continue'
	if s.Post != nil {
		cont = fn.newBasicBlock("for.post")
	}
	if label != nil {
		label._break = done
		label._continue = cont
	}
	emitJump(fn, loop)
	fn.currentBlock = loop
	if loop != body {
		b.cond(fn, s.Cond, body, done)
		fn.currentBlock = body
	}
	fn.targets = &targets{
		tail:      fn.targets,
		_break:    done,
		_continue: cont,
	}
	b.stmt(fn, s.Body)
	fn.targets = fn.targets.tail
	emitJump(fn, cont)

	if s.Post != nil {
		fn.currentBlock = cont
		b.stmt(fn, s.Post)
		emitJump(fn, loop) // back-edge
	}
	fn.currentBlock = done
}

// rangeIndexed emits to fn the header for an integer-indexed loop
// over array, *array or slice value x.
// The v result is defined only if tv is non-nil.
// forPos is the position of the "for" token.
//
func (b *builder) rangeIndexed(fn *Function, x Value, tv types.Type, pos syntax.Pos) (k, v Value, loop, done *BasicBlock) {
	//
	//      length = len(x)
	//      index = -1
	// loop:                                   (target of continue)
	//      index++
	// 	if index < length goto body else done
	// body:
	//      k = index
	//      v = x[index]
	//      ...body...
	// 	jump loop
	// done:                                   (target of break)

	// Determine number of iterations.
	var length Value
	if arr, ok := deref(x.Type()).Underlying().(*types.Array); ok {
		// For array or *array, the number of iterations is
		// known statically thanks to the type.  We avoid a
		// data dependence upon x, permitting later dead-code
		// elimination if x is pure, static unrolling, etc.
		// Ranging over a nil *array may have >0 iterations.
		// We still generate code for x, in case it has effects.
		length = intConst(arr.Len())
	} else {
		// length = len(x).
		var c Call
		c.Call.Value = makeLen(x.Type())
		c.Call.Args = []Value{x}
		c.setType(tInt)
		length = fn.emit(&c)
	}

	index := fn.addLocal(tInt, syntax.NoPos)
	emitStore(fn, index, intConst(-1), pos)

	loop = fn.newBasicBlock("rangeindex.loop")
	emitJump(fn, loop)
	fn.currentBlock = loop

	incr := &BinOp{
		Op: syntax.Add,
		X:  emitLoad(fn, index),
		Y:  vOne,
	}
	incr.setType(tInt)
	emitStore(fn, index, fn.emit(incr), pos)

	body := fn.newBasicBlock("rangeindex.body")
	done = fn.newBasicBlock("rangeindex.done")
	emitIf(fn, emitCompare(fn, syntax.Lss, incr, length, syntax.NoPos), body, done)
	fn.currentBlock = body

	k = emitLoad(fn, index)
	if tv != nil {
		switch t := x.Type().Underlying().(type) {
		case *types.Array:
			instr := &Index{
				X:     x,
				Index: k,
			}
			instr.setType(t.Elem())
			instr.setPos(x.Pos())
			v = fn.emit(instr)

		case *types.Pointer: // *array
			instr := &IndexAddr{
				X:     x,
				Index: k,
			}
			instr.setType(types.NewPointer(t.Elem().Underlying().(*types.Array).Elem()))
			instr.setPos(x.Pos())
			v = emitLoad(fn, fn.emit(instr))

		case *types.Slice:
			instr := &IndexAddr{
				X:     x,
				Index: k,
			}
			instr.setType(types.NewPointer(t.Elem()))
			instr.setPos(x.Pos())
			v = emitLoad(fn, fn.emit(instr))

		default:
			panic("rangeIndexed x:" + t.String())
		}
	}
	return
}

// rangeIter emits to fn the header for a loop using
// Range/Next/Extract to iterate over map or string value x.
// tk and tv are the types of the key/value results k and v, or nil
// if the respective component is not wanted.
//
func (b *builder) rangeIter(fn *Function, x Value, tk, tv types.Type, pos syntax.Pos) (k, v Value, loop, done *BasicBlock) {
	//
	//	it = range x
	// loop:                                   (target of continue)
	//	okv = next it                      (ok, key, value)
	//  	ok = extract okv #0
	// 	if ok goto body else done
	// body:
	// 	k = extract okv #1
	// 	v = extract okv #2
	//      ...body...
	// 	jump loop
	// done:                                   (target of break)
	//

	if tk == nil {
		tk = tInvalid
	}
	if tv == nil {
		tv = tInvalid
	}

	rng := &Range{X: x}
	rng.setPos(pos)
	rng.setType(tRangeIter)
	it := fn.emit(rng)

	loop = fn.newBasicBlock("rangeiter.loop")
	emitJump(fn, loop)
	fn.currentBlock = loop

	_, isString := x.Type().Underlying().(*types.Basic)

	okv := &Next{
		Iter:     it,
		IsString: isString,
	}
	okv.setType(types.NewTuple(
		varOk,
		newVar("k", tk),
		newVar("v", tv),
	))
	fn.emit(okv)

	body := fn.newBasicBlock("rangeiter.body")
	done = fn.newBasicBlock("rangeiter.done")
	emitIf(fn, emitExtract(fn, okv, 0), body, done)
	fn.currentBlock = body

	if tk != tInvalid {
		k = emitExtract(fn, okv, 1)
	}
	if tv != tInvalid {
		v = emitExtract(fn, okv, 2)
	}
	return
}

// rangeChan emits to fn the header for a loop that receives from
// channel x until it fails.
// tk is the channel's element type, or nil if the k result is
// not wanted
// pos is the position of the '=' or ':=' token.
//
func (b *builder) rangeChan(fn *Function, x Value, tk types.Type, pos syntax.Pos) (k Value, loop, done *BasicBlock) {
	//
	// loop:                                   (target of continue)
	//      ko = <-x                           (key, ok)
	//      ok = extract ko #1
	//      if ok goto body else done
	// body:
	//      k = extract ko #0
	//      ...
	//      goto loop
	// done:                                   (target of break)

	loop = fn.newBasicBlock("rangechan.loop")
	emitJump(fn, loop)
	fn.currentBlock = loop
	recv := &UnOp{
		Op:      syntax.Recv,
		X:       x,
		CommaOk: true,
	}
	recv.setPos(pos)
	recv.setType(types.NewTuple(
		newVar("k", x.Type().Underlying().(*types.Chan).Elem()),
		varOk,
	))
	ko := fn.emit(recv)
	body := fn.newBasicBlock("rangechan.body")
	done = fn.newBasicBlock("rangechan.done")
	emitIf(fn, emitExtract(fn, ko, 1), body, done)
	fn.currentBlock = body
	if tk != nil {
		k = emitExtract(fn, ko, 0)
	}
	return
}

// rangeStmt emits to fn code for the range statement s, optionally
// labelled by label.
//
func (b *builder) rangeStmt(fn *Function, s *syntax.ForStmt, label *lblock) {
	clause := s.Init.(*syntax.RangeClause)
	lhs := unpackExprList(clause.Lhs)

	var tk, tv types.Type
	if len(lhs) >= 1 && !isBlankIdent(lhs[0]) {
		tk = fn.Pkg.typeOf(lhs[0])
	}
	if len(lhs) >= 2 && !isBlankIdent(lhs[1]) {
		tv = fn.Pkg.typeOf(lhs[1])
	}

	// If iteration variables are defined (:=), this
	// occurs once outside the loop.
	//
	// Unlike a short variable declaration, a RangeStmt
	// using := never redeclares an existing variable; it
	// always creates a new one.
	if clause.Def {
		if tk != nil {
			fn.addLocalForIdent(lhs[0].(*syntax.Name))
		}
		if tv != nil {
			fn.addLocalForIdent(lhs[1].(*syntax.Name))
		}
	}

	x := b.expr(fn, clause.X)

	var k, v Value
	var loop, done *BasicBlock
	switch rt := x.Type().Underlying().(type) {
	case *types.Slice, *types.Array, *types.Pointer: // *array
		k, v, loop, done = b.rangeIndexed(fn, x, tv, s.Pos() /*For*/)

	case *types.Chan:
		k, loop, done = b.rangeChan(fn, x, tk, s.Pos() /*For*/)

	case *types.Map, *types.Basic: // string
		k, v, loop, done = b.rangeIter(fn, x, tk, tv, s.Pos() /*For*/)

	default:
		panic("Cannot range over: " + rt.String())
	}

	// Evaluate both LHS expressions before we update either.
	var kl, vl lvalue
	if tk != nil {
		kl = b.addr(fn, lhs[0], false) // non-escaping
	}
	if tv != nil {
		vl = b.addr(fn, lhs[1], false) // non-escaping
	}
	if tk != nil {
		kl.store(fn, k)
	}
	if tv != nil {
		vl.store(fn, v)
	}

	if label != nil {
		label._break = done
		label._continue = loop
	}

	fn.targets = &targets{
		tail:      fn.targets,
		_break:    done,
		_continue: loop,
	}
	b.stmt(fn, s.Body)
	fn.targets = fn.targets.tail
	emitJump(fn, loop) // back-edge
	fn.currentBlock = done
}

// stmt lowers statement s to SSA form, emitting code to fn.
func (b *builder) stmt(fn *Function, _s syntax.Stmt) {
	// The label of the current statement.  If non-nil, its _goto
	// target is always set; its _break and _continue are set only
	// within the body of switch/typeswitch/select/for/range.
	// It is effectively an additional default-nil parameter of stmt().
	var label *lblock
start:
	switch s := _s.(type) {
	case *syntax.EmptyStmt:
		// ignore.  (Usually removed by gofmt.)

	case *syntax.DeclStmt: // Con, Var or Typ
		for _, d := range s.Decl.SpecList {
			if d, ok := d.(*syntax.VarSpec); ok {
				b.localValueSpec(fn, d)
			}
		}

	case *syntax.LabeledStmt:
		label = fn.labelledBlock(s.Label)
		emitJump(fn, label._goto)
		fn.currentBlock = label._goto
		_s = s.Stmt
		goto start // effectively: tailcall stmt(fn, s.Stmt, label)

	case *syntax.ExprStmt:
		b.expr(fn, s.X)

	case *syntax.SendStmt:
		fn.emit(&Send{
			Chan: b.expr(fn, s.Chan),
			X: emitConv(fn, b.expr(fn, s.Value),
				fn.Pkg.typeOf(s.Chan).Underlying().(*types.Chan).Elem()),
			pos: s.Pos(), /*Arrow*/
		})

	case *syntax.AssignStmt:
		if s.Rhs == nil { // IncDecStmt
			loc := b.addr(fn, s.Lhs, false)
			b.assignOp(fn, loc, NewSSAConst(constant.MakeInt64(1), loc.typ()), s.Op, s.Pos())
		} else { // AssignStmt
			switch s.Op {
			case 0, syntax.Def:
				b.assignStmt(fn, unpackExprList(s.Lhs), unpackExprList(s.Rhs), s.Op == syntax.Def)
			default: // +=, etc.
				b.assignOp(fn, b.addr(fn, s.Lhs, false), b.expr(fn, s.Rhs), s.Op, s.Pos())
			}
		}

	case *syntax.CallStmt:
		switch s.Tok {
		case syntax.Go:
			// The "intrinsics" new/make/len/cap are forbidden here.
			// panic is treated like an ordinary function call.
			v := SSAGo{pos: s.Pos() /*Go*/}
			b.setCall(fn, s.Call, &v.Call)
			fn.emit(&v)

		case syntax.Defer:
			// The "intrinsics" new/make/len/cap are forbidden here.
			// panic is treated like an ordinary function call.
			v := SSADefer{pos: s.Pos() /*Defer*/}
			b.setCall(fn, s.Call, &v.Call)
			fn.emit(&v)

			// A deferred call can cause recovery from panic,
			// and control resumes at the Recover block.
			createRecoverBlock(fn)

		default:
			panic("unexpected s.Tok")
		}

	case *syntax.ReturnStmt:
		var results []Value
		if len(unpackExprList(s.Results)) == 1 && fn.Signature.Results().Len() > 1 {
			// Return of one expression in a multi-valued function.
			tuple := b.exprN(fn, s.Results)
			ttuple := tuple.Type().(*types.Tuple)
			for i, n := 0, ttuple.Len(); i < n; i++ {
				results = append(results,
					emitConv(fn, emitExtract(fn, tuple, i),
						fn.Signature.Results().At(i).Type()))
			}
		} else {
			// 1:1 return, or no-arg return in non-void function.
			for i, r := range unpackExprList(s.Results) {
				v := emitConv(fn, b.expr(fn, r), fn.Signature.Results().At(i).Type())
				results = append(results, v)
			}
		}
		if fn.namedResults != nil {
			// Function has named result parameters (NRPs).
			// Perform parallel assignment of return operands to NRPs.
			for i, r := range results {
				emitStore(fn, fn.namedResults[i], r, s.Pos() /*Return*/)
			}
		}
		// Run function calls deferred in this
		// function when explicitly returning from it.
		fn.emit(new(RunDefers))
		if fn.namedResults != nil {
			// Reload NRPs to form the result tuple.
			results = results[:0]
			for _, r := range fn.namedResults {
				results = append(results, emitLoad(fn, r))
			}
		}
		fn.emit(&Return{Results: results, pos: s.Pos() /*Return*/})
		fn.currentBlock = fn.newBasicBlock("unreachable")

	case *syntax.BranchStmt:
		var block *BasicBlock
		switch s.Tok {
		case syntax.Break:
			if s.Label != nil {
				block = fn.labelledBlock(s.Label)._break
			} else {
				for t := fn.targets; t != nil && block == nil; t = t.tail {
					block = t._break
				}
			}

		case syntax.Continue:
			if s.Label != nil {
				block = fn.labelledBlock(s.Label)._continue
			} else {
				for t := fn.targets; t != nil && block == nil; t = t.tail {
					block = t._continue
				}
			}

		case syntax.Fallthrough:
			for t := fn.targets; t != nil && block == nil; t = t.tail {
				block = t._fallthrough
			}

		case syntax.Goto:
			block = fn.labelledBlock(s.Label)._goto
		}
		emitJump(fn, block)
		fn.currentBlock = fn.newBasicBlock("unreachable")

	case *syntax.BlockStmt:
		b.stmtList(fn, s.List)

	case *syntax.IfStmt:
		if s.Init != nil {
			b.stmt(fn, s.Init)
		}
		then := fn.newBasicBlock("if.then")
		done := fn.newBasicBlock("if.done")
		els := done
		if s.Else != nil {
			els = fn.newBasicBlock("if.else")
		}
		b.cond(fn, s.Cond, then, els)
		fn.currentBlock = then
		b.stmt(fn, s.Then)
		emitJump(fn, done)

		if s.Else != nil {
			fn.currentBlock = els
			b.stmt(fn, s.Else)
			emitJump(fn, done)
		}

		fn.currentBlock = done

	case *syntax.SwitchStmt:
		if _, ok := s.Tag.(*syntax.TypeSwitchGuard); ok {
			b.typeSwitchStmt(fn, s, label)
		} else {
			b.switchStmt(fn, s, label)
		}

	case *syntax.SelectStmt:
		b.selectStmt(fn, s, label)

	case *syntax.ForStmt:
		if _, ok := s.Init.(*syntax.RangeClause); ok {
			b.rangeStmt(fn, s, label)
		} else {
			b.forStmt(fn, s, label)
		}

	default:
		panic(fmt.Sprintf("unexpected statement kind: %T", s))
	}
}

// buildFunction builds SSA code for the body of function fn.  Idempotent.
func (b *builder) buildFunction(fn *Function) {
	if fn.Blocks != nil {
		return // building already started
	}

	var recvField *syntax.Field
	var body *syntax.BlockStmt
	var functype *syntax.FuncType
	switch n := fn.syntax.(type) {
	case nil:
		return // not a Go source function.  (Synthetic, or from object file.)
	case *syntax.FuncDecl:
		functype = n.Type
		recvField = n.Recv
		body = n.Body
	case *syntax.FuncLit:
		functype = n.Type
		body = n.Body
	default:
		panic(n)
	}

	if body == nil {
		// External function.
		if fn.Params == nil {
			// This condition ensures we add a non-empty
			// params list once only, but we may attempt
			// the degenerate empty case repeatedly.
			// TODO(adonovan): opt: don't do that.

			// We set Function.Params even though there is no body
			// code to reference them.  This simplifies clients.
			if recv := fn.Signature.Recv(); recv != nil {
				fn.addParamObj(recv)
			}
			params := fn.Signature.Params()
			for i, n := 0, params.Len(); i < n; i++ {
				fn.addParamObj(params.At(i))
			}
		}
		return
	}
	if fn.Prog.mode&LogSource != 0 {
		defer logStack("build function %s @ %s", fn, fn.pos)()
	}
	fn.startBody()
	fn.createSyntacticParams(recvField, functype)
	b.stmt(fn, body)
	if cb := fn.currentBlock; cb != nil && (cb == fn.Blocks[0] || cb == fn.Recover || cb.Preds != nil) {
		// Control fell off the end of the function's body block.
		//
		// Block optimizations eliminate the current block, if
		// unreachable.  It is a builder invariant that
		// if this no-arg return is ill-typed for
		// fn.Signature.Results, this block must be
		// unreachable.  The sanity checker checks this.
		fn.emit(new(RunDefers))
		fn.emit(new(Return))
	}
	fn.finishBody()
}

// buildFuncDecl builds SSA code for the function or method declared
// by decl in package pkg.
//
func (b *builder) buildFuncDecl(pkg *SSAPackage, decl *syntax.FuncDecl) {
	id := decl.Name
	if isBlankIdent(id) {
		return // discard
	}
	fn := pkg.values[pkg.info.Defs[id]].(*Function)
	if decl.Recv == nil && id.Value == "init" {
		var v Call
		v.Call.Value = fn
		v.setType(types.NewTuple())
		pkg.init.emit(&v)
	}
	b.buildFunction(fn)
}

// Build calls Package.Build for each package in prog.
// Building occurs in parallel unless the BuildSerially mode flag was set.
//
// Build is intended for whole-program analysis; a typical compiler
// need only build a single package.
//
// Build is idempotent and thread-safe.
//
func (prog *Program) Build() {
	var wg sync.WaitGroup
	for _, p := range prog.packages {
		if prog.mode&BuildSerially != 0 {
			p.Build()
		} else {
			wg.Add(1)
			go func(p *SSAPackage) {
				p.Build()
				wg.Done()
			}(p)
		}
	}
	wg.Wait()
}

// Build builds SSA code for all functions and vars in package p.
//
// Precondition: CreatePackage must have been called for all of p's
// direct imports (and hence its direct imports must have been
// error-free).
//
// Build is idempotent and thread-safe.
//
func (p *SSAPackage) Build() { p.buildOnce.Do(p.build) }

func (p *SSAPackage) build() {
	if p.info == nil {
		return // synthetic package, e.g. "testmain"
	}

	// Ensure we have runtime type info for all exported members.
	// TODO(adonovan): ideally belongs in memberFromObject, but
	// that would require package creation in topological order.
	for name, mem := range p.Members {
		if token.IsExported(name) {
			p.Prog.needMethodsOf(mem.Type())
		}
	}
	if p.Prog.mode&LogSource != 0 {
		defer logStack("build %s", p)()
	}
	init := p.init
	init.startBody()

	var done *BasicBlock

	if p.Prog.mode&BareInits == 0 {
		// Make init() skip if package is already initialized.
		initguard := p.Var("init$guard")
		doinit := init.newBasicBlock("init.start")
		done = init.newBasicBlock("init.done")
		emitIf(init, emitLoad(init, initguard), done, doinit)
		init.currentBlock = doinit
		emitStore(init, initguard, vTrue, syntax.NoPos)

		// Call the init() function of each package we import.
		for _, pkg := range p.Pkg.Imports() {
			prereq := p.Prog.packages[pkg]
			if prereq == nil {
				panic(fmt.Sprintf("Package(%q).Build(): unsatisfied import: Program.CreatePackage(%q) was not called", p.Pkg.Path(), pkg.Path()))
			}
			var v Call
			v.Call.Value = prereq.init
			v.Call.pos = init.pos
			v.setType(types.NewTuple())
			init.emit(&v)
		}
	}

	var b builder

	// Initialize package-level vars in correct order.
	for _, varinit := range p.info.InitOrder {
		if init.Prog.mode&LogSource != 0 {
			fmt.Fprintf(os.Stderr, "build global initializer %v @ %s\n",
				varinit.Lhs, varinit.Rhs.Pos())
		}
		if len(varinit.Lhs) == 1 {
			// 1:1 initialization: var x, y = a(), b()
			var lval lvalue
			if v := varinit.Lhs[0]; v.Name() != "_" {
				lval = &address{addr: p.values[v].(*Global), pos: v.Pos()}
			} else {
				lval = blank{}
			}
			b.assign(init, lval, varinit.Rhs, true, nil)
		} else {
			// n:1 initialization: var x, y :=  f()
			tuple := b.exprN(init, varinit.Rhs)
			for i, v := range varinit.Lhs {
				if v.Name() == "_" {
					continue
				}
				emitStore(init, p.values[v].(*Global), emitExtract(init, tuple, i), v.Pos())
			}
		}
	}

	// Build all package-level functions, init functions
	// and methods, including unreachable/blank ones.
	// We build them in source order, but it's not significant.
	for _, file := range p.files {
		for _, decl := range file.DeclList {
			if decl, ok := decl.(*syntax.FuncDecl); ok {
				b.buildFuncDecl(p, decl)
			}
		}
	}

	// Finish up init().
	if p.Prog.mode&BareInits == 0 {
		emitJump(init, done)
		init.currentBlock = done
	}
	init.emit(new(Return))
	init.finishBody()

	p.info = nil // We no longer need ASTs or github.com/mdempsky/amigo/types deductions.

	if p.Prog.mode&SanityCheckFunctions != 0 {
		sanityCheckPackage(p)
	}
}

// Like ObjectOf, but panics instead of returning nil.
// Only valid during p's create and build phases.
func (p *SSAPackage) objectOf(id *syntax.Name) types.Object {
	if o := p.info.ObjectOf(id); o != nil {
		return o
	}
	panic(fmt.Sprintf("no types.Object for syntax.Name %s @ %s",
		id.Value, id.Pos()))
}

// Like TypeOf, but panics instead of returning nil.
// Only valid during p's create and build phases.
func (p *SSAPackage) typeOf(e syntax.Expr) types.Type {
	if T := p.info.TypeOf(e); T != nil {
		return T
	}
	panic(fmt.Sprintf("no type for %T @ %s",
		e, e.Pos()))
}

func unpackExprList(e syntax.Expr) []syntax.Expr {
	switch e := e.(type) {
	case nil:
		return nil
	case *syntax.ListExpr:
		return e.ElemList
	default:
		return []syntax.Expr{e}
	}
}
