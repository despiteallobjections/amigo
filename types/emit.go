// Copyright 2013 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package types

// Helpers for emitting SSA instructions.

import (
	"fmt"

	. "github.com/mdempsky/amigo/syntax"
)

// emitNew emits to f a new (heap Alloc) instruction allocating an
// object of type typ.  pos is the optional source location.
//
func emitNew(b *builder, typ Type, pos Pos) *Alloc {
	v := &Alloc{Heap: true}
	v.setType(NewPointer(typ))
	v.setPos(pos)
	b.emit(v)
	return v
}

// emitLoad emits to f an instruction to load the address addr into a
// new temporary, and returns the value so defined.
//
func emitLoad(b *builder, addr Value) *UnOp {
	v := &UnOp{Op: Mul, X: addr}
	v.setType(ssaDeref(addr.Type()))
	b.emit(v)
	return v
}

// emitDebugRef emits to f a DebugRef pseudo-instruction associating
// expression e with value v.
//
func emitDebugRef(b *builder, e Expr, v Value, isAddr bool) {
	if !b.Fn.debugInfo() {
		return // debugging not enabled
	}
	if v == nil || e == nil {
		panic("nil")
	}
	var obj Object
	e = Unparen(e)
	if id, ok := e.(*Name); ok {
		if isBlankIdent(id) {
			return
		}
		obj = b.Fn.Pkg.objectOf(id)
		switch obj.(type) {
		case *Nil, *Const, *Builtin:
			return
		}
	}
	b.emit(&DebugRef{
		X:      v,
		Expr:   e,
		IsAddr: isAddr,
		object: obj,
	})
}

// emitArith emits to f code to compute the binary operation op(x, y)
// where op is an eager shift, logical or arithmetic operation.
// (Use emitCompare() for comparisons and Builder.logicalBinop() for
// non-eager operations.)
//
func emitArith(b *builder, op Operator, x, y Value, t Type, pos Pos) Value {
	switch op {
	case Shl, Shr:
		x = emitConv(b, x, t)
		// y may be signed or an 'untyped' constant.
		// TODO(adonovan): whence signed values?
		if yt, ok := y.Type().Underlying().(*Basic); ok && yt.Info()&IsUnsigned == 0 {
			y = emitConv(b, y, Typ[Uint64])
		}

	case Add, Sub, Mul, Div, Rem, And, Or, Xor, AndNot:
		x = emitConv(b, x, t)
		y = emitConv(b, y, t)

	default:
		panic("illegal op in emitArith: " + op.String())

	}
	v := &BinOp{
		Op: op,
		X:  x,
		Y:  y,
	}
	v.setPos(pos)
	v.setType(t)
	return b.emit(v)
}

// emitCompare emits to f code compute the boolean result of
// comparison comparison 'x op y'.
//
func emitCompare(b *builder, op Operator, x, y Value, pos Pos) Value {
	xt := x.Type().Underlying()
	yt := y.Type().Underlying()

	// Special case to optimise a tagless SwitchStmt so that
	// these are equivalent
	//   switch { case e: ...}
	//   switch true { case e: ... }
	//   if e==true { ... }
	// even in the case when e's type is an interface.
	// TODO(adonovan): opt: generalise to x==true, false!=y, etc.
	if x == vTrue && op == Eql {
		if yt, ok := yt.(*Basic); ok && yt.Info()&IsBoolean != 0 {
			return y
		}
	}

	if Identical(xt, yt) {
		// no conversion necessary
	} else if _, ok := xt.(*Interface); ok {
		y = emitConv(b, y, x.Type())
	} else if _, ok := yt.(*Interface); ok {
		x = emitConv(b, x, y.Type())
	} else if _, ok := x.(*SSAConst); ok {
		x = emitConv(b, x, y.Type())
	} else if _, ok := y.(*SSAConst); ok {
		y = emitConv(b, y, x.Type())
	} else {
		// other cases, e.g. channels.  No-op.
	}

	v := &BinOp{
		Op: op,
		X:  x,
		Y:  y,
	}
	v.setPos(pos)
	v.setType(tBool)
	return b.emit(v)
}

// isValuePreserving returns true if a conversion from ut_src to
// ut_dst is value-preserving, i.e. just a change of type.
// Precondition: neither argument is a named type.
//
func isValuePreserving(ut_src, ut_dst Type) bool {
	// Identical underlying types?
	if IdenticalIgnoreTags(ut_dst, ut_src) {
		return true
	}

	switch ut_dst.(type) {
	case *Chan:
		// Conversion between channel types?
		_, ok := ut_src.(*Chan)
		return ok

	case *Pointer:
		// Conversion between pointers with identical base types?
		_, ok := ut_src.(*Pointer)
		return ok
	}
	return false
}

// emitConv emits to f code to convert Value val to exactly type typ,
// and returns the converted value.  Implicit conversions are required
// by language assignability rules in assignments, parameter passing,
// etc.
//
func emitConv(b *builder, val Value, typ Type) Value {
	t_src := val.Type()

	// Identical types?  Conversion is a no-op.
	if Identical(t_src, typ) {
		return val
	}

	ut_dst := typ.Underlying()
	ut_src := t_src.Underlying()

	// Just a change of type, but not value or representation?
	if isValuePreserving(ut_src, ut_dst) {
		c := &ChangeType{X: val}
		c.setType(typ)
		return b.emit(c)
	}

	// Conversion to, or construction of a value of, an interface type?
	if _, ok := ut_dst.(*Interface); ok {
		// Assignment from one interface type to another?
		if _, ok := ut_src.(*Interface); ok {
			c := &ChangeInterface{X: val}
			c.setType(typ)
			return b.emit(c)
		}

		// Untyped nil constant?  Return interface-typed nil constant.
		if ut_src == tUntypedNil {
			return nilConst(typ)
		}

		// Convert (non-nil) "untyped" literals to their default type.
		if t, ok := ut_src.(*Basic); ok && t.Info()&IsUntyped != 0 {
			val = emitConv(b, val, Default(ut_src))
		}

		b.Fn.Pkg.Prog.needMethodsOf(val.Type())
		mi := &MakeInterface{X: val}
		mi.setType(typ)
		return b.emit(mi)
	}

	// Conversion of a compile-time constant value?
	if c, ok := val.(*SSAConst); ok {
		if _, ok := ut_dst.(*Basic); ok || c.IsNil() {
			// Conversion of a compile-time constant to
			// another constant type results in a new
			// constant of the destination type and
			// (initially) the same abstract value.
			// We don't truncate the value yet.
			return NewSSAConst(c.Value, typ)
		}

		// We're converting from constant to non-constant type,
		// e.g. string -> []byte/[]rune.
	}

	// Conversion from slice to array pointer?
	if slice, ok := ut_src.(*Slice); ok {
		if ptr, ok := ut_dst.(*Pointer); ok {
			if arr, ok := ptr.Elem().Underlying().(*Array); ok && Identical(slice.Elem(), arr.Elem()) {
				c := &SliceToArrayPointer{X: val}
				c.setType(ut_dst)
				return b.emit(c)
			}
		}
	}
	// A representation-changing conversion?
	// At least one of {ut_src,ut_dst} must be *Basic.
	// (The other may be []byte or []rune.)
	_, ok1 := ut_src.(*Basic)
	_, ok2 := ut_dst.(*Basic)
	if ok1 || ok2 {
		c := &Convert{X: val}
		c.setType(typ)
		return b.emit(c)
	}

	panic(fmt.Sprintf("in %s: cannot convert %s (%s) to %s", b, val, val.Type(), typ))
}

// emitStore emits to f an instruction to store value val at location
// addr, applying implicit conversions as required by assignability rules.
//
func emitStore(b *builder, addr, val Value, pos Pos) *Store {
	s := &Store{
		Addr: addr,
		Val:  emitConv(b, val, ssaDeref(addr.Type())),
		pos:  pos,
	}
	b.emit(s)
	return s
}

// emitJump emits to f a jump to target, and updates the control-flow graph.
// Postcondition: f.currentBlock is nil.
//
func emitJump(b *builder, target *BasicBlock) {
	block := b.currentBlock
	block.emit(new(Jump))
	addEdge(block, target)
	b.currentBlock = nil
}

// emitIf emits to f a conditional jump to tblock or fblock based on
// cond, and updates the control-flow graph.
// Postcondition: f.currentBlock is nil.
//
func emitIf(b *builder, cond Value, tblock, fblock *BasicBlock) {
	block := b.currentBlock
	block.emit(&If{Cond: cond})
	addEdge(block, tblock)
	addEdge(block, fblock)
	b.currentBlock = nil
}

// emitExtract emits to f an instruction to extract the index'th
// component of tuple.  It returns the extracted value.
//
func emitExtract(b *builder, tuple Value, index int) Value {
	e := &Extract{Tuple: tuple, Index: index}
	e.setType(tuple.Type().(*Tuple).At(index).Type())
	return b.emit(e)
}

// emitTypeAssert emits to f a type assertion value := x.(t) and
// returns the value.  x.Type() must be an interface.
//
func emitTypeAssert(b *builder, x Value, t Type, pos Pos) Value {
	a := &TypeAssert{X: x, AssertedType: t}
	a.setPos(pos)
	a.setType(t)
	return b.emit(a)
}

// emitTypeTest emits to f a type test value,ok := x.(t) and returns
// a (value, ok) tuple.  x.Type() must be an interface.
//
func emitTypeTest(b *builder, x Value, t Type, pos Pos) Value {
	a := &TypeAssert{
		X:            x,
		AssertedType: t,
		CommaOk:      true,
	}
	a.setPos(pos)
	a.setType(NewTuple(
		newVar("value", t),
		varOk,
	))
	return b.emit(a)
}

// emitTailCall emits to f a function call in tail position.  The
// caller is responsible for all fields of 'call' except its type.
// Intended for wrapper methods.
// Precondition: f does/will not use deferred procedure calls.
// Postcondition: f.currentBlock is nil.
//
func emitTailCall(b *builder, call *Call) {
	tresults := b.Fn.Signature.Results()
	nr := tresults.Len()
	if nr == 1 {
		call.typ = tresults.At(0).Type()
	} else {
		call.typ = tresults
	}
	tuple := b.emit(call)
	var ret Return
	switch nr {
	case 0:
		// no-op
	case 1:
		ret.Results = []Value{tuple}
	default:
		for i := 0; i < nr; i++ {
			v := emitExtract(b, tuple, i)
			// TODO(adonovan): in principle, this is required:
			//   v = emitConv(f, o.Type, f.Signature.Results[i].Type)
			// but in practice emitTailCall is only used when
			// the types exactly match.
			ret.Results = append(ret.Results, v)
		}
	}
	b.emit(&ret)
	b.currentBlock = nil
}

// emitImplicitSelections emits to f code to apply the sequence of
// implicit field selections specified by indices to base value v, and
// returns the selected value.
//
// If v is the address of a struct, the result will be the address of
// a field; if it is the value of a struct, the result will be the
// value of a field.
//
func emitImplicitSelections(b *builder, v Value, indices []int) Value {
	for _, index := range indices {
		fld := ssaDeref(v.Type()).Underlying().(*Struct).Field(index)

		if isPointer(v.Type()) {
			instr := &FieldAddr{
				X:     v,
				Field: index,
			}
			instr.setType(NewPointer(fld.Type()))
			v = b.emit(instr)
			// Load the field's value iff indirectly embedded.
			if isPointer(fld.Type()) {
				v = emitLoad(b, v)
			}
		} else {
			instr := &SSAField{
				X:     v,
				Field: index,
			}
			instr.setType(fld.Type())
			v = b.emit(instr)
		}
	}
	return v
}

// emitFieldSelection emits to f code to select the index'th field of v.
//
// If wantAddr, the input must be a pointer-to-struct and the result
// will be the field's address; otherwise the result will be the
// field's value.
// Ident id is used for position and debug info.
//
func emitFieldSelection(b *builder, v Value, index int, wantAddr bool, id *Name) Value {
	fld := ssaDeref(v.Type()).Underlying().(*Struct).Field(index)
	if isPointer(v.Type()) {
		instr := &FieldAddr{
			X:     v,
			Field: index,
		}
		instr.setPos(id.Pos())
		instr.setType(NewPointer(fld.Type()))
		v = b.emit(instr)
		// Load the field's value iff we don't want its address.
		if !wantAddr {
			v = emitLoad(b, v)
		}
	} else {
		instr := &SSAField{
			X:     v,
			Field: index,
		}
		instr.setPos(id.Pos())
		instr.setType(fld.Type())
		v = b.emit(instr)
	}
	emitDebugRef(b, id, v, wantAddr)
	return v
}

// zeroValue emits to f code to produce a zero value of type t,
// and returns it.
//
func zeroValue(b *builder, t Type) Value {
	switch t.Underlying().(type) {
	case *Struct, *Array:
		return emitLoad(b, b.addLocal(t, NoPos))
	default:
		return zeroConst(t)
	}
}

// createRecoverBlock emits to f a block of code to return after a
// recovered panic, and sets f.Recover to it.
//
// If f's result parameters are named, the code loads and returns
// their current values, otherwise it returns the zero values of their
// type.
//
// Idempotent.
//
func createRecoverBlock(b *builder) {
	fn := b.Fn
	if fn.Recover != nil {
		return // already created
	}
	saved := b.currentBlock

	fn.Recover = b.newBasicBlock("recover")
	b.currentBlock = b.Fn.Recover

	var results []Value
	if b.namedResults != nil {
		// Reload NRPs to form value tuple.
		for _, r := range b.namedResults {
			results = append(results, emitLoad(b, r))
		}
	} else {
		R := fn.Signature.Results()
		for i, n := 0, R.Len(); i < n; i++ {
			T := R.At(i).Type()

			// Return zero value of each result type.
			results = append(results, zeroValue(b, T))
		}
	}
	b.emit(&Return{Results: results})

	b.currentBlock = saved
}
