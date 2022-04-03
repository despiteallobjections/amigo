// Copyright 2013 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package types

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

	. "github.com/mdempsky/amigo/syntax"
)

type opaqueType struct {
	Type
	name string
}

func (t *opaqueType) String() string { return t.name }

var (
	varOk    = newVar("ok", tBool)
	varIndex = newVar("index", tInt)

	// Type constants.
	tBool       = Typ[Bool]
	tByte       = Typ[Byte]
	tInt        = Typ[Int]
	tInvalid    = Typ[Invalid]
	tString     = Typ[String]
	tUntypedNil = Typ[UntypedNil]
	tRangeIter  = &opaqueType{nil, "iter"} // the type of all "range" iterators
	tEface      = NewInterfaceType(nil, nil)

	// SSA Value constants.
	vZero = intConst(0)
	vOne  = intConst(1)
	vTrue = NewSSAConst(constant.MakeBool(true), tBool)
)

// builder holds state associated with the function currently being built.
// Its methods contain all the logic for AST-to-SSA conversion.
type builder struct {
	Prog *Program
	Fn   *Function
	Body *BlockStmt

	currentBlock *BasicBlock        // where to emit code
	objects      map[*Var]Value     // addresses of local variables
	namedResults []*Alloc           // tuple of named results
	targets      *targets           // linked stack of branch targets
	lblocks      map[string]*lblock // labelled blocks
}

func (b *builder) String() string { return b.Fn.String() }

// cond emits to fn code to evaluate boolean condition e and jump
// to t or f depending on its value, performing various simplifications.
//
// Postcondition: b.currentBlock is nil.
//
func (b *builder) cond(e Expr, t, f *BasicBlock) {
	switch e := e.(type) {
	case *ParenExpr:
		b.cond(e.X, t, f)
		return

	case *Operation:
		if e.Y != nil { // BinaryExpr
			switch e.Op {
			case AndAnd:
				ltrue := b.newBasicBlock("cond.true")
				b.cond(e.X, ltrue, f)
				b.currentBlock = ltrue
				b.cond(e.Y, t, f)
				return

			case OrOr:
				lfalse := b.newBasicBlock("cond.false")
				b.cond(e.X, t, lfalse)
				b.currentBlock = lfalse
				b.cond(e.Y, t, f)
				return
			}
		} else { // UnaryExpr
			if e.Op == Not {
				b.cond(e.X, f, t)
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
	emitIf(b, b.expr(e), t, f)
}

// logicalBinop emits code to fn to evaluate e, a &&- or
// ||-expression whose reified boolean value is wanted.
// The value is returned.
//
func (b *builder) logicalBinop(e *Operation) Value {
	rhs := b.newBasicBlock("binop.rhs")
	done := b.newBasicBlock("binop.done")

	// T(e) = T(e.X) = T(e.Y) after untyped constants have been
	// eliminated.
	// TODO(adonovan): not true; MyBool==MyBool yields UntypedBool.
	t := b.Fn.Pkg.typeOf(e)

	var short Value // value of the short-circuit path
	switch e.Op {
	case AndAnd:
		b.cond(e.X, rhs, done)
		short = NewSSAConst(constant.MakeBool(false), t)

	case OrOr:
		b.cond(e.X, done, rhs)
		short = NewSSAConst(constant.MakeBool(true), t)
	}

	// Is rhs unreachable?
	if rhs.Preds == nil {
		// Simplify false&&y to false, true||y to true.
		b.currentBlock = done
		return short
	}

	// Is done unreachable?
	if done.Preds == nil {
		// Simplify true&&y (or false||y) to y.
		b.currentBlock = rhs
		return b.expr(e.Y)
	}

	// All edges from e.X to done carry the short-circuit value.
	var edges []Value
	for range done.Preds {
		edges = append(edges, short)
	}

	// The edge from e.Y to done carries the value of e.Y.
	b.currentBlock = rhs
	edges = append(edges, b.expr(e.Y))
	emitJump(b, done)
	b.currentBlock = done

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
func (b *builder) exprN(e Expr) Value {
	typ := b.Fn.Pkg.typeOf(e).(*Tuple)
	switch e := e.(type) {
	case *ParenExpr:
		return b.exprN(e.X)

	case *CallExpr:
		// Currently, no built-in function nor type conversion
		// has multiple results, so we can avoid some of the
		// cases for single-valued CallExpr.
		var c Call
		b.setCall(e, &c.Call)
		c.typ = typ
		return b.emit(&c)

	case *IndexExpr:
		mapt := b.Fn.Pkg.typeOf(e.X).Underlying().(*Map)
		lookup := &Lookup{
			X:       b.expr(e.X),
			Index:   emitConv(b, b.expr(e.Index), mapt.Key()),
			CommaOk: true,
		}
		lookup.setType(typ)
		lookup.setPos(e.Pos() /*Lbrack*/)
		return b.emit(lookup)

	case *AssertExpr:
		return emitTypeTest(b, b.expr(e.X), typ.At(0).Type(), e.Pos() /*Lparen*/)

	case *Operation:
		unop := &UnOp{
			Op:      Recv,
			X:       b.expr(e.X),
			CommaOk: true,
		}
		unop.setType(typ)
		unop.setPos(e.Pos() /*OpPos*/)
		return b.emit(unop)
	}
	panic(fmt.Sprintf("exprN(%T) in %s", e, b.Fn))
}

// builtin emits to fn SSA instructions to implement a call to the
// built-in function obj with the specified arguments
// and return type.  It returns the value defined by the result.
//
// The result is nil if no special handling was required; in this case
// the caller should treat this like an ordinary library function
// call.
//
func (b *builder) builtin(obj *Builtin, args []Expr, typ Type, pos Pos) Value {
	switch obj.Name() {
	case "make":
		switch typ.Underlying().(type) {
		case *Slice:
			n := b.expr(args[1])
			m := n
			if len(args) == 3 {
				m = b.expr(args[2])
			}
			if m, ok := m.(*SSAConst); ok {
				// treat make([]T, n, m) as new([m]T)[:n]
				cap := m.Int64()
				at := NewArray(typ.Underlying().(*Slice).Elem(), cap)
				alloc := emitNew(b, at, pos)
				alloc.Comment = "makeslice"
				v := &SSASlice{
					X:    alloc,
					High: n,
				}
				v.setPos(pos)
				v.setType(typ)
				return b.emit(v)
			}
			v := &MakeSlice{
				Len: n,
				Cap: m,
			}
			v.setPos(pos)
			v.setType(typ)
			return b.emit(v)

		case *Map:
			var res Value
			if len(args) == 2 {
				res = b.expr(args[1])
			}
			v := &MakeMap{Reserve: res}
			v.setPos(pos)
			v.setType(typ)
			return b.emit(v)

		case *Chan:
			var sz Value = vZero
			if len(args) == 2 {
				sz = b.expr(args[1])
			}
			v := &MakeChan{Size: sz}
			v.setPos(pos)
			v.setType(typ)
			return b.emit(v)
		}

	case "new":
		alloc := emitNew(b, ssaDeref(typ), pos)
		alloc.Comment = "new"
		return alloc

	case "len", "cap":
		// Special case: len or cap of an array or *array is
		// based on the type, not the value which may be nil.
		// We must still evaluate the value, though.  (If it
		// was side-effect free, the whole call would have
		// been constant-folded.)
		t := ssaDeref(b.Fn.Pkg.typeOf(args[0])).Underlying()
		if at, ok := t.(*Array); ok {
			b.expr(args[0]) // for effects only
			return intConst(at.Len())
		}
		// Otherwise treat as normal.

	case "panic":
		b.emit(&Panic{
			X:   emitConv(b, b.expr(args[0]), tEface),
			pos: pos,
		})
		b.currentBlock = b.newBasicBlock("unreachable")
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
func (b *builder) addr(e Expr, escaping bool) lvalue {
	switch e := e.(type) {
	case *Name:
		if isBlankIdent(e) {
			return blank{}
		}
		obj := b.Fn.Pkg.objectOf(e).(*Var)
		v := b.Prog.packageLevelValue(obj) // var (address)
		if v == nil {
			v = b.lookup(b.Fn, obj, escaping)
		}
		return &address{addr: v, pos: e.Pos(), expr: e}

	case *CompositeLit:
		t := ssaDeref(b.Fn.Pkg.typeOf(e))
		var v *Alloc
		if escaping {
			v = emitNew(b, t, e.Pos() /*Lbrace*/)
		} else {
			v = b.addLocal(t, e.Pos() /*Lbrace*/)
		}
		v.Comment = "complit"
		var sb storebuf
		b.compLit(v, e, true, &sb)
		sb.emit(b)
		return &address{addr: v, pos: e.Pos() /*Lbrace*/, expr: e}

	case *ParenExpr:
		return b.addr(e.X, escaping)

	case *SelectorExpr:
		sel, ok := b.Fn.Pkg.info.Selections[e]
		if !ok {
			// qualified identifier
			return b.addr(e.Sel, escaping)
		}
		if sel.Kind() != FieldVal {
			panic(sel)
		}
		wantAddr := true
		v := b.receiver(e.X, wantAddr, escaping, sel)
		last := len(sel.Index()) - 1
		return &address{
			addr: emitFieldSelection(b, v, sel.Index()[last], true, e.Sel),
			pos:  e.Sel.Pos(),
			expr: e.Sel,
		}

	case *IndexExpr:
		var x Value
		var et Type
		switch t := b.Fn.Pkg.typeOf(e.X).Underlying().(type) {
		case *Array:
			x = b.addr(e.X, escaping).address(b)
			et = NewPointer(t.Elem())
		case *Pointer:
			x = b.expr(e.X)
			et = NewPointer(t.Elem().Underlying().(*Array).Elem())
		case *Slice:
			x = b.expr(e.X)
			et = NewPointer(t.Elem())
		case *Map:
			return &element{
				m:   b.expr(e.X),
				k:   emitConv(b, b.expr(e.Index), t.Key()),
				t:   t.Elem(),
				pos: e.Pos(), /*Lbrack*/
			}
		default:
			panic("unexpected container type in IndexExpr: " + t.String())
		}
		v := &IndexAddr{
			X:     x,
			Index: emitConv(b, b.expr(e.Index), tInt),
		}
		v.setPos(e.Pos() /*Lbrack*/)
		v.setType(et)
		return &address{addr: b.emit(v), pos: e.Pos() /*Lbrack*/, expr: e}

	case *Operation:
		return &address{addr: b.expr(e.X), pos: e.Pos() /*Star*/, expr: e}
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

func (sb *storebuf) emit(b *builder) {
	for _, s := range sb.stores {
		s.lhs.store(b, s.rhs)
	}
}

// assign emits to fn code to initialize the lvalue loc with the value
// of expression e.  If isZero is true, assign assumes that loc holds
// the zero value for its type.
//
// This is equivalent to loc.store(b.expr(e)), but may generate
// better code in some cases, e.g., for composite literals in an
// addressable location.
//
// If sb is not nil, assign generates code to evaluate expression e, but
// not to update loc.  Instead, the necessary stores are appended to the
// storebuf sb so that they can be executed later.  This allows correct
// in-place update of existing variables when the RHS is a composite
// literal that may reference parts of the LHS.
//
func (b *builder) assign(loc lvalue, e Expr, isZero bool, sb *storebuf) {
	// Can we initialize it in place?
	if e, ok := Unparen(e).(*CompositeLit); ok {
		// A CompositeLit never evaluates to a pointer,
		// so if the type of the location is a pointer,
		// an &-operation is implied.
		if _, ok := loc.(blank); !ok { // avoid calling blank.typ()
			if isPointer(loc.typ()) {
				ptr := b.addr(e, true).address(b)
				// copy address
				if sb != nil {
					sb.store(loc, ptr)
				} else {
					loc.store(b, ptr)
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
				addr := loc.address(b)
				if sb != nil {
					b.compLit(addr, e, isZero, sb)
				} else {
					var sb storebuf
					b.compLit(addr, e, isZero, &sb)
					sb.emit(b)
				}

				// Subtle: emit debug ref for aggregate types only;
				// slice and map are handled by store ops in compLit.
				switch loc.typ().Underlying().(type) {
				case *Struct, *Array:
					emitDebugRef(b, e, addr, true)
				}

				return
			}
		}
	}

	// simple case: just copy
	rhs := b.expr(e)
	if sb != nil {
		sb.store(loc, rhs)
	} else {
		loc.store(b, rhs)
	}
}

// expr lowers a single-result expression e to SSA form, emitting code
// to fn and returning the Value defined by the expression.
//
func (b *builder) expr(e Expr) Value {
	e = Unparen(e)

	tv := b.Fn.Pkg.info.Types[e]

	// Is expression a constant?
	if tv.Value != nil {
		return NewSSAConst(tv.Value, tv.Type)
	}

	var v Value
	if tv.Addressable() {
		// Prefer pointer arithmetic ({Index,Field}Addr) followed
		// by Load over subelement extraction (e.g. Index, Field),
		// to avoid large copies.
		v = b.addr(e, false).load(b)
	} else {
		v = b.expr0(e, tv)
	}
	if b.Fn.debugInfo() {
		emitDebugRef(b, e, v, false)
	}
	return v
}

func (b *builder) expr0(e Expr, tv TypeAndValue) Value {
	switch e := e.(type) {
	case *BasicLit:
		panic("non-constant BasicLit") // unreachable

	case *FuncLit:
		fn2 := &Function{
			name:      fmt.Sprintf("%s$%d", b.Fn.Name(), 1+len(b.Fn.AnonFuncs)),
			Signature: b.Fn.Pkg.typeOf(e.Type).Underlying().(*Signature),
			pos:       e.Type.Pos(), /*Func*/
			parent:    b.Fn,
			Pkg:       b.Fn.Pkg,
		}
		b.Fn.AnonFuncs = append(b.Fn.AnonFuncs, fn2)
		b.Prog.buildFunction(fn2, e.Body)
		if fn2.FreeVars == nil {
			return fn2
		}
		v := &MakeClosure{Fn: fn2}
		v.setType(tv.Type)
		for _, fv := range fn2.FreeVars {
			outer := b.lookup(b.Fn, fv.object, true) // escaping
			v.Bindings = append(v.Bindings, outer)
		}
		return b.emit(v)

	case *AssertExpr:
		return emitTypeAssert(b, b.expr(e.X), tv.Type, e.Pos() /*Lparen*/)

	case *CallExpr:
		if b.Fn.Pkg.info.Types[e.Fun].IsType() {
			// Explicit type conversion, e.g. string(x) or big.Int(x)
			x := b.expr(e.ArgList[0])
			y := emitConv(b, x, tv.Type)
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
		if id, ok := Unparen(e.Fun).(*Name); ok {
			if obj, ok := b.Fn.Pkg.info.Uses[id].(*Builtin); ok {
				if v := b.builtin(obj, e.ArgList, tv.Type, e.Pos() /*Lparen*/); v != nil {
					return v
				}
			}
		}
		// Regular function call.
		var v Call
		b.setCall(e, &v.Call)
		v.setType(tv.Type)
		return b.emit(&v)

	case *Operation:
		if e.Y == nil { // UnaryExpr
			switch e.Op {
			case And:
				addr := b.addr(e.X, true)
				if x, ok := Unparen(e.X).(*Operation); ok && x.Op == Mul {
					// &*p must panic if p is nil (http://golang.org/s/go12nil).
					// For simplicity, we'll just (suboptimally) rely
					// on the side effects of a load.
					// TODO(adonovan): emit dedicated nilcheck.
					addr.load(b)
				}
				return addr.address(b)
			case Add:
				return b.expr(e.X)
			case Not, Recv, Sub, Xor:
				v := &UnOp{
					Op: e.Op,
					X:  b.expr(e.X),
				}
				v.setPos(e.Pos() /*OpPos*/)
				v.setType(tv.Type)
				return b.emit(v)
			case Mul:
				// Addressable types (lvalues)
				return b.addr(e, false).load(b)
			default:
				panic(e.Op)
			}
		} else { // BinaryExpr
			switch e.Op {
			case AndAnd, OrOr:
				return b.logicalBinop(e)
			case Shl, Shr:
				fallthrough
			case Add, Sub, Mul, Div, Rem, And, Or, Xor, AndNot:
				return emitArith(b, e.Op, b.expr(e.X), b.expr(e.Y), tv.Type, e.Pos() /*OpPos*/)

			case Eql, Neq, Gtr, Lss, Leq, Geq:
				cmp := emitCompare(b, e.Op, b.expr(e.X), b.expr(e.Y), e.Pos() /*OpPos*/)
				// The type of x==y may be UntypedBool.
				return emitConv(b, cmp, Default(tv.Type))
			default:
				panic("illegal op in BinaryExpr: " + e.Op.String())
			}
		}

	case *SliceExpr:
		var low, high, max Value
		var x Value
		switch b.Fn.Pkg.typeOf(e.X).Underlying().(type) {
		case *Array:
			// Potentially escaping.
			x = b.addr(e.X, true).address(b)
		case *Basic, *Slice, *Pointer:
			x = b.expr(e.X)
		default:
			panic("unreachable")
		}
		// TODO(mdempsky): Why do we evaluate high before low?
		if e.Index[1] != nil {
			high = b.expr(e.Index[1])
		}
		if e.Index[0] != nil {
			low = b.expr(e.Index[0])
		}
		if e.Index[2] != nil {
			max = b.expr(e.Index[2])
		}
		v := &SSASlice{
			X:    x,
			Low:  low,
			High: high,
			Max:  max,
		}
		v.setPos(e.Pos() /*Lbrack*/)
		v.setType(tv.Type)
		return b.emit(v)

	case *Name:
		obj := b.Fn.Pkg.info.Uses[e]
		// Universal built-in or nil?
		switch obj := obj.(type) {
		case *Builtin:
			return &SSABuiltin{name: obj.Name(), sig: tv.Type.(*Signature)}
		case *Nil:
			return nilConst(tv.Type)
		}
		// Package-level func or var?
		if v := b.Prog.packageLevelValue(obj); v != nil {
			if _, ok := obj.(*Var); ok {
				return emitLoad(b, v) // var (address)
			}
			return v // (func)
		}
		// Local var.
		return emitLoad(b, b.lookup(b.Fn, obj.(*Var), false)) // var (address)

	case *SelectorExpr:
		sel, ok := b.Fn.Pkg.info.Selections[e]
		if !ok {
			// builtin unsafe.{Add,Slice}
			if obj, ok := b.Fn.Pkg.info.Uses[e.Sel].(*Builtin); ok {
				return &SSABuiltin{name: obj.Name(), sig: tv.Type.(*Signature)}
			}
			// qualified identifier
			return b.expr(e.Sel)
		}
		switch sel.Kind() {
		case MethodExpr:
			// (*T).f or T.f, the method f from the method-set of type T.
			// The result is a "thunk".
			return emitConv(b, b.Prog.makeThunk(sel), tv.Type)

		case MethodVal:
			// e.f where e is an expression and f is a method.
			// The result is a "bound".
			obj := sel.Obj().(*Func)
			rt := recvType(obj)
			wantAddr := isPointer(rt)
			escaping := true
			v := b.receiver(e.X, wantAddr, escaping, sel)
			if isInterface(rt) {
				// If v has interface type I,
				// we must emit a check that v is non-nil.
				// We use: typeassert v.(I).
				emitTypeAssert(b, v, rt, NoPos)
			}
			c := &MakeClosure{
				Fn:       b.Prog.makeBound(obj),
				Bindings: []Value{v},
			}
			c.setPos(e.Sel.Pos())
			c.setType(tv.Type)
			return b.emit(c)

		case FieldVal:
			indices := sel.Index()
			last := len(indices) - 1
			v := b.expr(e.X)
			v = emitImplicitSelections(b, v, indices[:last])
			v = emitFieldSelection(b, v, indices[last], false, e.Sel)
			return v
		}

		panic("unexpected expression-relative selector")

	case *IndexExpr:
		switch t := b.Fn.Pkg.typeOf(e.X).Underlying().(type) {
		case *Array:
			// Non-addressable array (in a register).
			v := &Index{
				X:     b.expr(e.X),
				Index: emitConv(b, b.expr(e.Index), tInt),
			}
			v.setPos(e.Pos() /*Lbrack*/)
			v.setType(t.Elem())
			return b.emit(v)

		case *Map:
			// Maps are not addressable.
			mapt := b.Fn.Pkg.typeOf(e.X).Underlying().(*Map)
			v := &Lookup{
				X:     b.expr(e.X),
				Index: emitConv(b, b.expr(e.Index), mapt.Key()),
			}
			v.setPos(e.Pos() /*Lbrack*/)
			v.setType(mapt.Elem())
			return b.emit(v)

		case *Basic:
			// Strings are not addressable.
			v := &Lookup{
				X:     b.expr(e.X),
				Index: b.expr(e.Index),
			}
			v.setPos(e.Pos() /*Lbrack*/)
			v.setType(tByte)
			return b.emit(v)

		case *Slice, *Pointer:
			// Addressable slice/array; use IndexAddr and Load.
			return b.addr(e, false).load(b)

		default:
			panic("unexpected container type in IndexExpr: " + t.String())
		}

	case *CompositeLit:
		// Addressable types (lvalues)
		return b.addr(e, false).load(b)
	}

	panic(fmt.Sprintf("unexpected expr: %T", e))
}

// stmtList emits to fn code for all statements in list.
func (b *builder) stmtList(list []Stmt) {
	for _, s := range list {
		b.stmt(s)
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
func (b *builder) receiver(e Expr, wantAddr, escaping bool, sel *Selection) Value {
	var v Value
	if wantAddr && !sel.Indirect() && !isPointer(b.Fn.Pkg.typeOf(e)) {
		v = b.addr(e, escaping).address(b)
	} else {
		v = b.expr(e)
	}

	last := len(sel.Index()) - 1
	v = emitImplicitSelections(b, v, sel.Index()[:last])
	if !wantAddr && isPointer(v.Type()) {
		v = emitLoad(b, v)
	}
	return v
}

// setCallFunc populates the function parts of a CallCommon structure
// (Func, Method, Recv, Args[0]) based on the kind of invocation
// occurring in e.
//
func (b *builder) setCallFunc(e *CallExpr, c *CallCommon) {
	c.pos = e.Pos() /*Lparen*/

	// Is this a method call?
	if selector, ok := Unparen(e.Fun).(*SelectorExpr); ok {
		sel, ok := b.Fn.Pkg.info.Selections[selector]
		if ok && sel.Kind() == MethodVal {
			obj := sel.Obj().(*Func)
			recv := recvType(obj)
			wantAddr := isPointer(recv)
			escaping := true
			v := b.receiver(selector.X, wantAddr, escaping, sel)
			if isInterface(recv) {
				// Invoke-mode call.
				c.Value = v
				c.Method = obj
			} else {
				// "Call"-mode call.
				c.Value = b.Prog.declaredFunc(obj)
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
	c.Value = b.expr(e.Fun)
}

// emitCallArgs emits to f code for the actual parameters of call e to
// a (possibly built-in) function of effective type sig.
// The argument values are appended to args, which is then returned.
//
func (b *builder) emitCallArgs(sig *Signature, e *CallExpr, args []Value) []Value {
	// f(x, y, z...): pass slice z straight through.
	if e.HasDots {
		for i, arg := range e.ArgList {
			v := emitConv(b, b.expr(arg), sig.Params().At(i).Type())
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
		v := b.expr(arg)
		if ttuple, ok := v.Type().(*Tuple); ok { // MRV chain
			for i, n := 0, ttuple.Len(); i < n; i++ {
				args = append(args, emitExtract(b, v, i))
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
		args[offset+i] = emitConv(b, args[offset+i], sig.Params().At(i).Type())
	}

	// Actual->formal assignability conversions for variadic parameter,
	// and construction of slice.
	if sig.Variadic() {
		varargs := args[offset+np:]
		st := sig.Params().At(np).Type().(*Slice)
		vt := st.Elem()
		if len(varargs) == 0 {
			args = append(args, nilConst(st))
		} else {
			// Replace a suffix of args with a slice containing it.
			at := NewArray(vt, int64(len(varargs)))
			a := emitNew(b, at, NoPos)
			a.setPos(e.Pos() /*Rparen*/)
			a.Comment = "varargs"
			for i, arg := range varargs {
				iaddr := &IndexAddr{
					X:     a,
					Index: intConst(int64(i)),
				}
				iaddr.setType(NewPointer(vt))
				b.emit(iaddr)
				emitStore(b, iaddr, arg, arg.Pos())
			}
			s := &SSASlice{X: a}
			s.setType(st)
			args[offset+np] = b.emit(s)
			args = args[:offset+np+1]
		}
	}
	return args
}

// setCall emits to fn code to evaluate all the parameters of a function
// call e, and populates *c with those values.
//
func (b *builder) setCall(e *CallExpr, c *CallCommon) {
	// First deal with the f(...) part and optional receiver.
	b.setCallFunc(e, c)

	// Then append the other actual parameters.
	sig, _ := b.Fn.Pkg.typeOf(e.Fun).Underlying().(*Signature)
	if sig == nil {
		panic(fmt.Sprintf("no signature for call of %s", e.Fun))
	}
	c.Args = b.emitCallArgs(sig, e, c.Args)
}

// assignOp emits to fn code to perform loc <op>= val.
func (b *builder) assignOp(loc lvalue, val Value, op Operator, pos Pos) {
	oldv := loc.load(b)
	loc.store(b, emitArith(b, op, oldv, emitConv(b, val, oldv.Type()), loc.typ(), pos))
}

// localValueSpec emits to fn code to define all of the vars in the
// function-local ValueSpec, spec.
//
func (b *builder) localValueSpec(spec *VarSpec) {
	values := unpackExpr(spec.Values)

	switch {
	case len(values) == len(spec.NameList):
		// e.g. var x, y = 0, 1
		// 1:1 assignment
		for i, id := range spec.NameList {
			if !isBlankIdent(id) {
				b.addLocalForIdent(id)
			}
			lval := b.addr(id, false) // non-escaping
			b.assign(lval, values[i], true, nil)
		}

	case len(values) == 0:
		// e.g. var x, y int
		// Locals are implicitly zero-initialized.
		for _, id := range spec.NameList {
			if !isBlankIdent(id) {
				lhs := b.addLocalForIdent(id)
				if b.Fn.debugInfo() {
					emitDebugRef(b, id, lhs, true)
				}
			}
		}

	default:
		// e.g. var x, y = pos()
		tuple := b.exprN(values[0])
		for i, id := range spec.NameList {
			if !isBlankIdent(id) {
				b.addLocalForIdent(id)
				lhs := b.addr(id, false) // non-escaping
				lhs.store(b, emitExtract(b, tuple, i))
			}
		}
	}
}

// assignStmt emits code to fn for a parallel assignment of rhss to lhss.
// isDef is true if this is a short variable declaration (:=).
//
// Note the similarity with localValueSpec.
//
func (b *builder) assignStmt(lhss, rhss []Expr, isDef bool) {
	// Side effects of all LHSs and RHSs must occur in left-to-right order.
	lvals := make([]lvalue, len(lhss))
	isZero := make([]bool, len(lhss))
	for i, lhs := range lhss {
		var lval lvalue = blank{}
		if !isBlankIdent(lhs) {
			if isDef {
				if obj := b.Fn.Pkg.info.Defs[lhs.(*Name)]; obj != nil {
					b.addNamedLocal(obj.(*Var))
					isZero[i] = true
				}
			}
			lval = b.addr(lhs, false) // non-escaping
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
			b.assign(lvals[i], rhss[i], isZero[i], &sb)
		}
		sb.emit(b)
	} else {
		// e.g. x, y = pos()
		tuple := b.exprN(rhss[0])
		emitDebugRef(b, rhss[0], tuple, false)
		for i, lval := range lvals {
			lval.store(b, emitExtract(b, tuple, i))
		}
	}
}

// arrayLen returns the length of the array whose composite literal elements are elts.
func (b *builder) arrayLen(elts []Expr) int64 {
	var max int64 = -1
	var i int64 = -1
	for _, e := range elts {
		if kv, ok := e.(*KeyValueExpr); ok {
			i = b.expr(kv.Key).(*SSAConst).Int64()
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
func (b *builder) compLit(addr Value, e *CompositeLit, isZero bool, sb *storebuf) {
	typ := ssaDeref(b.Fn.Pkg.typeOf(e))
	switch t := typ.Underlying().(type) {
	case *Struct:
		if !isZero && len(e.ElemList) != t.NumFields() {
			// memclear
			sb.store(&address{addr, e.Pos() /*Lbrace*/, nil},
				zeroValue(b, ssaDeref(addr.Type())))
			isZero = true
		}
		for i, e := range e.ElemList {
			fieldIndex := i
			pos := e.Pos()
			if kv, ok := e.(*KeyValueExpr); ok {
				fname := kv.Key.(*Name).Value
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
			faddr.setType(NewPointer(sf.Type()))
			b.emit(faddr)
			b.assign(&address{addr: faddr, pos: pos, expr: e}, e, isZero, sb)
		}

	case *Array, *Slice:
		var at *Array
		var array Value
		switch t := t.(type) {
		case *Slice:
			at = NewArray(t.Elem(), b.arrayLen(e.ElemList))
			alloc := emitNew(b, at, e.Pos() /*Lbrace*/)
			alloc.Comment = "slicelit"
			array = alloc
		case *Array:
			at = t
			array = addr

			if !isZero && int64(len(e.ElemList)) != at.Len() {
				// memclear
				sb.store(&address{array, e.Pos() /*Lbrace*/, nil},
					zeroValue(b, ssaDeref(array.Type())))
			}
		}

		var idx *SSAConst
		for _, e := range e.ElemList {
			pos := e.Pos()
			if kv, ok := e.(*KeyValueExpr); ok {
				idx = b.expr(kv.Key).(*SSAConst)
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
			iaddr.setType(NewPointer(at.Elem()))
			b.emit(iaddr)
			if t != at { // slice
				// backing array is unaliased => storebuf not needed.
				b.assign(&address{addr: iaddr, pos: pos, expr: e}, e, true, nil)
			} else {
				b.assign(&address{addr: iaddr, pos: pos, expr: e}, e, true, sb)
			}
		}

		if t != at { // slice
			s := &SSASlice{X: array}
			s.setPos(e.Pos() /*Lbrace*/)
			s.setType(typ)
			sb.store(&address{addr: addr, pos: e.Pos() /*Lbrace*/, expr: e}, b.emit(s))
		}

	case *Map:
		m := &MakeMap{Reserve: intConst(int64(len(e.ElemList)))}
		m.setPos(e.Pos() /*Lbrace*/)
		m.setType(typ)
		b.emit(m)
		for _, e := range e.ElemList {
			e := e.(*KeyValueExpr)

			// If a key expression in a map literal is itself a
			// composite literal, the type may be omitted.
			// For example:
			//	map[*struct{}]bool{{}: true}
			// An &-operation may be implied:
			//	map[*struct{}]bool{&struct{}{}: true}
			var key Value
			if _, ok := Unparen(e.Key).(*CompositeLit); ok && isPointer(t.Key()) {
				// A CompositeLit never evaluates to a pointer,
				// so if the type of the location is a pointer,
				// an &-operation is implied.
				key = b.addr(e.Key, true).address(b)
			} else {
				key = b.expr(e.Key)
			}

			loc := element{
				m:   m,
				k:   emitConv(b, key, t.Key()),
				t:   t.Elem(),
				pos: e.Pos(), /*Colon*/
			}

			// We call assign() only because it takes care
			// of any &-operation required in the recursive
			// case, e.g.,
			// map[int]*struct{}{0: {}} implies &struct{}{}.
			// In-place update is of course impossible,
			// and no storebuf is needed.
			b.assign(&loc, e.Value, true, nil)
		}
		sb.store(&address{addr: addr, pos: e.Pos() /*Lbrace*/, expr: e}, m)

	default:
		panic("unexpected CompositeLit type: " + t.String())
	}
}

// switchStmt emits to fn code for the switch statement s, optionally
// labelled by label.
//
func (b *builder) switchStmt(s *SwitchStmt, label *lblock) {
	// We treat SwitchStmt like a sequential if-else chain.
	// Multiway dispatch can be recovered later by ssautil.Switches()
	// to those cases that are free of side effects.
	if s.Init != nil {
		b.stmt(s.Init)
	}
	var tag Value = vTrue
	if s.Tag != nil {
		tag = b.expr(s.Tag)
	}
	done := b.newBasicBlock("switch.done")
	if label != nil {
		label._break = done
	}
	// We pull the default case (if present) down to the end.
	// But each fallthrough label must point to the next
	// body block in source order, so we preallocate a
	// body block (fallthru) for the next case.
	// Unfortunately this makes for a confusing block order.
	var dfltBody *[]Stmt
	var dfltFallthrough *BasicBlock
	var fallthru, dfltBlock *BasicBlock
	ncases := len(s.Body)
	for i, clause := range s.Body {
		body := fallthru
		if body == nil {
			body = b.newBasicBlock("switch.body") // first case only
		}

		// Preallocate body block for the next case.
		fallthru = done
		if i+1 < ncases {
			fallthru = b.newBasicBlock("switch.body")
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
		for _, cond := range unpackExpr(cc.Cases) {
			nextCond = b.newBasicBlock("switch.next")
			// TODO(adonovan): opt: when tag==vTrue, we'd
			// get better code if we use b.cond(cond)
			// instead of BinOp(EQL, tag, b.expr(cond))
			// followed by If.  Don't forget conversions
			// though.
			cond := emitCompare(b, Eql, tag, b.expr(cond), NoPos)
			emitIf(b, cond, body, nextCond)
			b.currentBlock = nextCond
		}
		b.currentBlock = body
		b.targets = &targets{
			tail:         b.targets,
			_break:       done,
			_fallthrough: fallthru,
		}
		b.stmtList(cc.Body)
		b.targets = b.targets.tail
		emitJump(b, done)
		b.currentBlock = nextCond
	}
	if dfltBlock != nil {
		emitJump(b, dfltBlock)
		b.currentBlock = dfltBlock
		b.targets = &targets{
			tail:         b.targets,
			_break:       done,
			_fallthrough: dfltFallthrough,
		}
		b.stmtList(*dfltBody)
		b.targets = b.targets.tail
	}
	emitJump(b, done)
	b.currentBlock = done
}

// typeSwitchStmt emits to fn code for the type switch statement s, optionally
// labelled by label.
//
func (b *builder) typeSwitchStmt(s *SwitchStmt, label *lblock) {
	guard := s.Tag.(*TypeSwitchGuard)

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
		b.stmt(s.Init)
	}

	x := b.expr(guard.X)

	done := b.newBasicBlock("typeswitch.done")
	if label != nil {
		label._break = done
	}
	var default_ *CaseClause
	for _, clause := range s.Body {
		cc := clause
		if cc.Cases == nil {
			default_ = cc
			continue
		}
		body := b.newBasicBlock("typeswitch.body")
		var next *BasicBlock
		var casetype Type
		var ti Value // ti, ok := typeassert,ok x <Ti>
		for _, cond := range unpackExpr(cc.Cases) {
			next = b.newBasicBlock("typeswitch.next")
			casetype = b.Fn.Pkg.typeOf(cond)
			var condv Value
			if casetype == tUntypedNil {
				condv = emitCompare(b, Eql, x, nilConst(x.Type()), NoPos)
				ti = x
			} else {
				yok := emitTypeTest(b, x, casetype, cc.Pos() /*Case*/)
				ti = emitExtract(b, yok, 0)
				condv = emitExtract(b, yok, 1)
			}
			emitIf(b, condv, body, next)
			b.currentBlock = next
		}
		if len(unpackExpr(cc.Cases)) != 1 {
			ti = x
		}
		b.currentBlock = body
		b.typeCaseBody(cc, ti, done)
		b.currentBlock = next
	}
	if default_ != nil {
		b.typeCaseBody(default_, x, done)
	} else {
		emitJump(b, done)
	}
	b.currentBlock = done
}

func (b *builder) typeCaseBody(cc *CaseClause, x Value, done *BasicBlock) {
	if obj := b.Fn.Pkg.info.Implicits[cc]; obj != nil {
		// In a switch y := x.(type), each case clause
		// implicitly declares a distinct object y.
		// In a single-type case, y has that type.
		// In multi-type cases, 'case nil' and default,
		// y has the same type as the interface operand.
		emitStore(b, b.addNamedLocal(obj.(*Var)), x, obj.Pos())
	}
	b.targets = &targets{
		tail:   b.targets,
		_break: done,
	}
	b.stmtList(cc.Body)
	b.targets = b.targets.tail
	emitJump(b, done)
}

// selectStmt emits to fn code for the select statement s, optionally
// labelled by label.
//
func (b *builder) selectStmt(s *SelectStmt, label *lblock) {
	// A blocking select of a single case degenerates to a
	// simple send or receive.
	// TODO(adonovan): opt: is this optimization worth its weight?
	if len(s.Body) == 1 {
		clause := s.Body[0]
		if clause.Comm != nil {
			b.stmt(clause.Comm)
			done := b.newBasicBlock("select.done")
			if label != nil {
				label._break = done
			}
			b.targets = &targets{
				tail:   b.targets,
				_break: done,
			}
			b.stmtList(clause.Body)
			b.targets = b.targets.tail
			emitJump(b, done)
			b.currentBlock = done
			return
		}
	}

	// First evaluate all channels in all cases, and find
	// the directions of each state.
	var states []*SelectState
	blocking := true
	debugInfo := b.Fn.debugInfo()
	for _, clause := range s.Body {
		var st *SelectState
		switch comm := clause.Comm.(type) {
		case nil: // default case
			blocking = false
			continue

		case *SendStmt:
			ch := b.expr(comm.Chan)
			st = &SelectState{
				Dir:  SendOnly,
				Chan: ch,
				Send: emitConv(b, b.expr(comm.Value),
					ch.Type().Underlying().(*Chan).Elem()),
				Pos: comm.Pos(), /*Arrow*/
			}
			if debugInfo {
				st.DebugNode = comm
			}

		case *AssignStmt:
			recv := Unparen(comm.Rhs).(*Operation)
			st = &SelectState{
				Dir:  RecvOnly,
				Chan: b.expr(recv.X),
				Pos:  recv.Pos(), /*OpPos*/
			}
			if debugInfo {
				st.DebugNode = recv
			}

		case *ExprStmt:
			recv := Unparen(comm.X).(*Operation)
			st = &SelectState{
				Dir:  RecvOnly,
				Chan: b.expr(recv.X),
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
	var vars []*Var
	vars = append(vars, varIndex, varOk)
	for _, st := range states {
		if st.Dir == RecvOnly {
			tElem := st.Chan.Type().Underlying().(*Chan).Elem()
			vars = append(vars, anonVar(tElem))
		}
	}
	sel.setType(NewTuple(vars...))

	b.emit(sel)
	idx := emitExtract(b, sel, 0)

	done := b.newBasicBlock("select.done")
	if label != nil {
		label._break = done
	}

	var defaultBody *[]Stmt
	state := 0
	r := 2 // index in 'sel' tuple of value; increments if st.Dir==RECV
	for _, cc := range s.Body {
		clause := cc
		if clause.Comm == nil {
			defaultBody = &clause.Body
			continue
		}
		body := b.newBasicBlock("select.body")
		next := b.newBasicBlock("select.next")
		emitIf(b, emitCompare(b, Eql, idx, intConst(int64(state)), NoPos), body, next)
		b.currentBlock = body
		b.targets = &targets{
			tail:   b.targets,
			_break: done,
		}
		switch comm := clause.Comm.(type) {
		case *ExprStmt:
			if debugInfo {
				v := emitExtract(b, sel, r)
				emitDebugRef(b, states[state].DebugNode.(Expr), v, false)
			}
			r++

		case *AssignStmt:
			lhs := unpackExpr(comm.Lhs)

			if comm.Op == Def {
				b.addLocalForIdent(lhs[0].(*Name))
			}
			x := b.addr(lhs[0], false) // non-escaping
			v := emitExtract(b, sel, r)
			if debugInfo {
				emitDebugRef(b, states[state].DebugNode.(Expr), v, false)
			}
			x.store(b, v)

			if len(lhs) == 2 { // x, ok := ...
				if comm.Op == Def {
					b.addLocalForIdent(lhs[1].(*Name))
				}
				ok := b.addr(lhs[1], false) // non-escaping
				ok.store(b, emitExtract(b, sel, 1))
			}
			r++
		}
		b.stmtList(clause.Body)
		b.targets = b.targets.tail
		emitJump(b, done)
		b.currentBlock = next
		state++
	}
	if defaultBody != nil {
		b.targets = &targets{
			tail:   b.targets,
			_break: done,
		}
		b.stmtList(*defaultBody)
		b.targets = b.targets.tail
	} else {
		// A blocking select must match some case.
		// (This should really be a runtime.errorString, not a string.)
		b.emit(&Panic{
			X: emitConv(b, stringConst("blocking select matched no case"), tEface),
		})
		b.currentBlock = b.newBasicBlock("unreachable")
	}
	emitJump(b, done)
	b.currentBlock = done
}

// forStmt emits to fn code for the for statement s, optionally
// labelled by label.
//
func (b *builder) forStmt(s *ForStmt, label *lblock) {
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
		b.stmt(s.Init)
	}
	body := b.newBasicBlock("for.body")
	done := b.newBasicBlock("for.done") // target of 'break'
	loop := body                        // target of back-edge
	if s.Cond != nil {
		loop = b.newBasicBlock("for.loop")
	}
	cont := loop // target of 'continue'
	if s.Post != nil {
		cont = b.newBasicBlock("for.post")
	}
	if label != nil {
		label._break = done
		label._continue = cont
	}
	emitJump(b, loop)
	b.currentBlock = loop
	if loop != body {
		b.cond(s.Cond, body, done)
		b.currentBlock = body
	}
	b.targets = &targets{
		tail:      b.targets,
		_break:    done,
		_continue: cont,
	}
	b.stmt(s.Body)
	b.targets = b.targets.tail
	emitJump(b, cont)

	if s.Post != nil {
		b.currentBlock = cont
		b.stmt(s.Post)
		emitJump(b, loop) // back-edge
	}
	b.currentBlock = done
}

// rangeIndexed emits to fn the header for an integer-indexed loop
// over array, *array or slice value x.
// The v result is defined only if tv is non-nil.
// forPos is the position of the "for" token.
//
func (b *builder) rangeIndexed(x Value, tv Type, pos Pos) (k, v Value, loop, done *BasicBlock) {
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
	if arr, ok := ssaDeref(x.Type()).Underlying().(*Array); ok {
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
		length = b.emit(&c)
	}

	index := b.addLocal(tInt, NoPos)
	emitStore(b, index, intConst(-1), pos)

	loop = b.newBasicBlock("rangeindex.loop")
	emitJump(b, loop)
	b.currentBlock = loop

	incr := &BinOp{
		Op: Add,
		X:  emitLoad(b, index),
		Y:  vOne,
	}
	incr.setType(tInt)
	emitStore(b, index, b.emit(incr), pos)

	body := b.newBasicBlock("rangeindex.body")
	done = b.newBasicBlock("rangeindex.done")
	emitIf(b, emitCompare(b, Lss, incr, length, NoPos), body, done)
	b.currentBlock = body

	k = emitLoad(b, index)
	if tv != nil {
		switch t := x.Type().Underlying().(type) {
		case *Array:
			instr := &Index{
				X:     x,
				Index: k,
			}
			instr.setType(t.Elem())
			instr.setPos(x.Pos())
			v = b.emit(instr)

		case *Pointer:
			instr := &IndexAddr{
				X:     x,
				Index: k,
			}
			instr.setType(NewPointer(t.Elem().Underlying().(*Array).Elem()))
			instr.setPos(x.Pos())
			v = emitLoad(b, b.emit(instr))

		case *Slice:
			instr := &IndexAddr{
				X:     x,
				Index: k,
			}
			instr.setType(NewPointer(t.Elem()))
			instr.setPos(x.Pos())
			v = emitLoad(b, b.emit(instr))

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
func (b *builder) rangeIter(x Value, tk, tv Type, pos Pos) (k, v Value, loop, done *BasicBlock) {
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
	it := b.emit(rng)

	loop = b.newBasicBlock("rangeiter.loop")
	emitJump(b, loop)
	b.currentBlock = loop

	_, isString := x.Type().Underlying().(*Basic)

	okv := &Next{
		Iter:     it,
		IsString: isString,
	}
	okv.setType(NewTuple(
		varOk,
		newVar("k", tk),
		newVar("v", tv),
	))
	b.emit(okv)

	body := b.newBasicBlock("rangeiter.body")
	done = b.newBasicBlock("rangeiter.done")
	emitIf(b, emitExtract(b, okv, 0), body, done)
	b.currentBlock = body

	if tk != tInvalid {
		k = emitExtract(b, okv, 1)
	}
	if tv != tInvalid {
		v = emitExtract(b, okv, 2)
	}
	return
}

// rangeChan emits to fn the header for a loop that receives from
// channel x until it fails.
// tk is the channel's element type, or nil if the k result is
// not wanted
// pos is the position of the '=' or ':=' token.
//
func (b *builder) rangeChan(x Value, tk Type, pos Pos) (k Value, loop, done *BasicBlock) {
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

	loop = b.newBasicBlock("rangechan.loop")
	emitJump(b, loop)
	b.currentBlock = loop
	recv := &UnOp{
		Op:      Recv,
		X:       x,
		CommaOk: true,
	}
	recv.setPos(pos)
	recv.setType(NewTuple(
		newVar("k", x.Type().Underlying().(*Chan).Elem()),
		varOk,
	))
	ko := b.emit(recv)
	body := b.newBasicBlock("rangechan.body")
	done = b.newBasicBlock("rangechan.done")
	emitIf(b, emitExtract(b, ko, 1), body, done)
	b.currentBlock = body
	if tk != nil {
		k = emitExtract(b, ko, 0)
	}
	return
}

// rangeStmt emits to fn code for the range statement s, optionally
// labelled by label.
//
func (b *builder) rangeStmt(s *ForStmt, label *lblock) {
	clause := s.Init.(*RangeClause)
	lhs := unpackExpr(clause.Lhs)

	var tk, tv Type
	if len(lhs) >= 1 && !isBlankIdent(lhs[0]) {
		tk = b.Fn.Pkg.typeOf(lhs[0])
	}
	if len(lhs) >= 2 && !isBlankIdent(lhs[1]) {
		tv = b.Fn.Pkg.typeOf(lhs[1])
	}

	// If iteration variables are defined (:=), this
	// occurs once outside the loop.
	//
	// Unlike a short variable declaration, a RangeStmt
	// using := never redeclares an existing variable; it
	// always creates a new one.
	if clause.Def {
		if tk != nil {
			b.addLocalForIdent(lhs[0].(*Name))
		}
		if tv != nil {
			b.addLocalForIdent(lhs[1].(*Name))
		}
	}

	x := b.expr(clause.X)

	var k, v Value
	var loop, done *BasicBlock
	switch rt := x.Type().Underlying().(type) {
	case *Slice, *Array, *Pointer:
		k, v, loop, done = b.rangeIndexed(x, tv, s.Pos() /*For*/)

	case *Chan:
		k, loop, done = b.rangeChan(x, tk, s.Pos() /*For*/)

	case *Map, *Basic:
		k, v, loop, done = b.rangeIter(x, tk, tv, s.Pos() /*For*/)

	default:
		panic("Cannot range over: " + rt.String())
	}

	// Evaluate both LHS expressions before we update either.
	var kl, vl lvalue
	if tk != nil {
		kl = b.addr(lhs[0], false) // non-escaping
	}
	if tv != nil {
		vl = b.addr(lhs[1], false) // non-escaping
	}
	if tk != nil {
		kl.store(b, k)
	}
	if tv != nil {
		vl.store(b, v)
	}

	if label != nil {
		label._break = done
		label._continue = loop
	}

	b.targets = &targets{
		tail:      b.targets,
		_break:    done,
		_continue: loop,
	}
	b.stmt(s.Body)
	b.targets = b.targets.tail
	emitJump(b, loop) // back-edge
	b.currentBlock = done
}

// stmt lowers statement s to SSA form, emitting code to fn.
func (b *builder) stmt(_s Stmt) {
	// The label of the current statement.  If non-nil, its _goto
	// target is always set; its _break and _continue are set only
	// within the body of switch/typeswitch/select/for/range.
	// It is effectively an additional default-nil parameter of stmt().
	var label *lblock
start:
	switch s := _s.(type) {
	case *EmptyStmt:
		// ignore.  (Usually removed by gofmt.)

	case *DeclStmt:
		for _, d := range s.Decl.SpecList {
			if d, ok := d.(*VarSpec); ok {
				b.localValueSpec(d)
			}
		}

	case *LabeledStmt:
		label = b.labelledBlock(s.Label)
		emitJump(b, label._goto)
		b.currentBlock = label._goto
		_s = s.Stmt
		goto start // effectively: tailcall stmt(s.Stmt, label)

	case *ExprStmt:
		b.expr(s.X)

	case *SendStmt:
		b.emit(&Send{
			Chan: b.expr(s.Chan),
			X: emitConv(b, b.expr(s.Value),
				b.Fn.Pkg.typeOf(s.Chan).Underlying().(*Chan).Elem()),
			pos: s.Pos(), /*Arrow*/
		})

	case *AssignStmt:
		if s.Rhs == nil { // IncDecStmt
			loc := b.addr(s.Lhs, false)
			b.assignOp(loc, NewSSAConst(constant.MakeInt64(1), loc.typ()), s.Op, s.Pos())
		} else { // AssignStmt
			switch s.Op {
			case 0, Def:
				b.assignStmt(unpackExpr(s.Lhs), unpackExpr(s.Rhs), s.Op == Def)
			default: // +=, etc.
				b.assignOp(b.addr(s.Lhs, false), b.expr(s.Rhs), s.Op, s.Pos())
			}
		}

	case *CallStmt:
		switch s.Tok {
		case Go:
			// The "intrinsics" new/make/len/cap are forbidden here.
			// panic is treated like an ordinary function call.
			v := SSAGo{pos: s.Pos() /*Go*/}
			b.setCall(s.Call, &v.Call)
			b.emit(&v)

		case Defer:
			// The "intrinsics" new/make/len/cap are forbidden here.
			// panic is treated like an ordinary function call.
			v := SSADefer{pos: s.Pos() /*Defer*/}
			b.setCall(s.Call, &v.Call)
			b.emit(&v)

			// A deferred call can cause recovery from panic,
			// and control resumes at the Recover block.
			createRecoverBlock(b)

		default:
			panic("unexpected s.Tok")
		}

	case *ReturnStmt:
		var results []Value
		if len(unpackExpr(s.Results)) == 1 && b.Fn.Signature.Results().Len() > 1 {
			// Return of one expression in a multi-valued function.
			tuple := b.exprN(s.Results)
			ttuple := tuple.Type().(*Tuple)
			for i, n := 0, ttuple.Len(); i < n; i++ {
				results = append(results,
					emitConv(b, emitExtract(b, tuple, i),
						b.Fn.Signature.Results().At(i).Type()))
			}
		} else {
			// 1:1 return, or no-arg return in non-void function.
			for i, r := range unpackExpr(s.Results) {
				v := emitConv(b, b.expr(r), b.Fn.Signature.Results().At(i).Type())
				results = append(results, v)
			}
		}
		if b.namedResults != nil {
			// Function has named result parameters (NRPs).
			// Perform parallel assignment of return operands to NRPs.
			for i, r := range results {
				emitStore(b, b.namedResults[i], r, s.Pos() /*Return*/)
			}
		}
		// Run function calls deferred in this
		// function when explicitly returning from it.
		b.emit(new(RunDefers))
		if b.namedResults != nil {
			// Reload NRPs to form the result tuple.
			results = results[:0]
			for _, r := range b.namedResults {
				results = append(results, emitLoad(b, r))
			}
		}
		b.emit(&Return{Results: results, pos: s.Pos() /*Return*/})
		b.currentBlock = b.newBasicBlock("unreachable")

	case *BranchStmt:
		var block *BasicBlock
		switch s.Tok {
		case Break:
			if s.Label != nil {
				block = b.labelledBlock(s.Label)._break
			} else {
				for t := b.targets; t != nil && block == nil; t = t.tail {
					block = t._break
				}
			}

		case Continue:
			if s.Label != nil {
				block = b.labelledBlock(s.Label)._continue
			} else {
				for t := b.targets; t != nil && block == nil; t = t.tail {
					block = t._continue
				}
			}

		case Fallthrough:
			for t := b.targets; t != nil && block == nil; t = t.tail {
				block = t._fallthrough
			}

		case Goto:
			block = b.labelledBlock(s.Label)._goto
		}
		emitJump(b, block)
		b.currentBlock = b.newBasicBlock("unreachable")

	case *BlockStmt:
		b.stmtList(s.List)

	case *IfStmt:
		if s.Init != nil {
			b.stmt(s.Init)
		}
		then := b.newBasicBlock("if.then")
		done := b.newBasicBlock("if.done")
		els := done
		if s.Else != nil {
			els = b.newBasicBlock("if.else")
		}
		b.cond(s.Cond, then, els)
		b.currentBlock = then
		b.stmt(s.Then)
		emitJump(b, done)

		if s.Else != nil {
			b.currentBlock = els
			b.stmt(s.Else)
			emitJump(b, done)
		}

		b.currentBlock = done

	case *SwitchStmt:
		if _, ok := s.Tag.(*TypeSwitchGuard); ok {
			b.typeSwitchStmt(s, label)
		} else {
			b.switchStmt(s, label)
		}

	case *SelectStmt:
		b.selectStmt(s, label)

	case *ForStmt:
		if _, ok := s.Init.(*RangeClause); ok {
			b.rangeStmt(s, label)
		} else {
			b.forStmt(s, label)
		}

	default:
		panic(fmt.Sprintf("unexpected statement kind: %T", s))
	}
}

// buildFunction builds SSA code for the body of function fn.  Idempotent.
func (prog *Program) buildFunction(fn *Function, body *BlockStmt) {
	b := &builder{Prog: prog, Fn: fn, Body: body}

	if fn.Blocks != nil {
		return // building already started
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
			if recv := b.Fn.Signature.Recv(); recv != nil {
				b.addParamObj(recv)
			}
			params := b.Fn.Signature.Params()
			for i, n := 0, params.Len(); i < n; i++ {
				b.addParamObj(params.At(i))
			}
		}
		return
	}
	if b.Prog.mode&LogSource != 0 {
		defer logStack("build function %s @ %s", fn, fn.pos)()
	}
	b.startBody()
	b.createSyntacticParams()
	b.stmt(body)
	if cb := b.currentBlock; cb != nil && (cb == fn.Blocks[0] || cb == fn.Recover || cb.Preds != nil) {
		// Control fell off the end of the function's body block.
		//
		// Block optimizations eliminate the current block, if
		// unreachable.  It is a builder invariant that
		// if this no-arg return is ill-typed for
		// b.Fn.Signature.Results, this block must be
		// unreachable.  The sanity checker checks this.
		b.emit(new(RunDefers))
		b.emit(new(Return))
	}
	b.finishBody()
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
			p.Build(prog)
		} else {
			wg.Add(1)
			go func(p *SSAPackage) {
				p.Build(prog)
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
func (p *SSAPackage) Build(prog *Program) { p.buildOnce.Do(func() { p.build(prog) }) }

func (p *SSAPackage) build(prog *Program) {
	if p.info == nil {
		return // synthetic package, e.g. "testmain"
	}

	if prog.mode&LogSource != 0 {
		defer logStack("build %s", p)()
	}

	// Build all package-level functions, init functions
	// and methods.
	// We build them in source order, but it's not significant.
	for _, file := range p.files {
		for _, decl := range file.DeclList {
			if decl, ok := decl.(*FuncDecl); ok {
				if obj := p.info.Defs[decl.Name].(*Func); obj.Name() != "_" {
					prog.buildFunction(obj.member, decl.Body)
				}
			}
		}
	}

	// Ensure we have runtime type info for all exported members.
	// TODO(adonovan): ideally belongs in memberFromObject, but
	// that would require package creation in topological order.
	pkgScope := p.Pkg.Scope()
	for _, name := range pkgScope.Names() {
		if token.IsExported(name) {
			obj := pkgScope.Lookup(name)
			typ := obj.Type()

			// TestRuntimeTypes expects to see *T in the list of runtime
			// types whene there's a global variable of type T.
			//
			// TODO(mdempsky): Is that important? Can we just update the
			// test expectations instead?
			if _, ok := obj.(*Var); ok {
				typ = NewPointer(typ)
			}

			prog.needMethodsOf(typ)
		}
	}

	init := p.Init.member
	b := &builder{Prog: prog, Fn: init}

	b.startBody()

	var done *BasicBlock

	if prog.mode&BareInits == 0 {
		// Make init() skip if package is already initialized.
		initguard := p.Var("init$guard")
		doinit := b.newBasicBlock("init.start")
		done = b.newBasicBlock("init.done")
		emitIf(b, emitLoad(b, initguard), done, doinit)
		b.currentBlock = doinit
		emitStore(b, initguard, vTrue, NoPos)

		// Call the init() function of each package we import.
		for _, pkg := range p.Pkg.Imports() {
			prereq := prog.packages[pkg]
			if prereq == nil {
				panic(fmt.Sprintf("Package(%q).Build(): unsatisfied import: Program.CreatePackage(%q) was not called", p.Pkg.Path(), pkg.Path()))
			}
			var v Call
			v.Call.Value = prereq.Init.member
			v.Call.pos = init.pos
			v.setType(NewTuple())
			b.emit(&v)
		}
	}

	// Initialize package-level vars in correct order.
	for _, varinit := range p.info.InitOrder {
		if prog.mode&LogSource != 0 {
			fmt.Fprintf(os.Stderr, "build global initializer %v @ %s\n",
				varinit.Lhs, varinit.Rhs.Pos())
		}
		if len(varinit.Lhs) == 1 {
			// 1:1 initialization: var x, y = a(), b()
			var lval lvalue
			if v := varinit.Lhs[0]; v.Name() != "_" {
				lval = &address{addr: v.member, pos: v.Pos()}
			} else {
				lval = blank{}
			}
			b.assign(lval, varinit.Rhs, true, nil)
		} else {
			// n:1 initialization: var x, y = f()
			tuple := b.exprN(varinit.Rhs)
			for i, v := range varinit.Lhs {
				if v.Name() == "_" {
					continue
				}
				emitStore(b, v.member, emitExtract(b, tuple, i), v.Pos())
			}
		}
	}

	// Call user declared init functions in source order.
	for _, file := range p.files {
		for _, decl := range file.DeclList {
			if decl, ok := decl.(*FuncDecl); ok && decl.Recv == nil && decl.Name.Value == "init" {
				obj := p.info.Defs[decl.Name].(*Func)
				var v Call
				v.Call.Value = obj.member
				v.setType(NewTuple())
				b.emit(&v)
			}
		}
	}

	// Finish up init().
	if prog.mode&BareInits == 0 {
		emitJump(b, done)
		b.currentBlock = done
	}
	b.emit(new(Return))
	b.finishBody()

	p.info = nil // We no longer need ASTs or github.com/mdempsky/amigo/types deductions.

	if prog.mode&SanityCheckFunctions != 0 {
		sanityCheckPackage(p)
	}
}

// Like ObjectOf, but panics instead of returning nil.
// Only valid during p's create and build phases.
func (p *SSAPackage) objectOf(id *Name) Object {
	if o := p.info.ObjectOf(id); o != nil {
		return o
	}
	panic(fmt.Sprintf("no types.Object for syntax.Name %s @ %s",
		id.Value, id.Pos()))
}

// Like TypeOf, but panics instead of returning nil.
// Only valid during p's create and build phases.
func (p *SSAPackage) typeOf(e Expr) Type {
	if T := p.info.TypeOf(e); T != nil {
		return T
	}
	panic(fmt.Sprintf("no type for %T @ %s",
		e, e.Pos()))
}
