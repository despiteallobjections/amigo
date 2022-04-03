// Copyright 2013 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package types

// lvalues are the union of addressable expressions and map-index
// expressions.

import (
	. "github.com/mdempsky/amigo/syntax"
)

// An lvalue represents an assignable location that may appear on the
// left-hand side of an assignment.  This is a generalization of a
// pointer to permit updates to elements of maps.
//
type lvalue interface {
	store(b *builder, v Value) // stores v into the location
	load(b *builder) Value     // loads the contents of the location
	address(b *builder) Value  // address of the location
	typ() Type                 // returns the type of the location
}

// An address is an lvalue represented by a true pointer.
type address struct {
	addr Value
	pos  Pos  // source position
	expr Expr // source syntax of the value (not address) [debug mode]
}

func (a *address) load(b *builder) Value {
	load := b.emitLoad(a.addr)
	load.pos = a.pos
	return load
}

func (a *address) store(b *builder, v Value) {
	store := b.emitStore(a.addr, v, a.pos)
	if a.expr != nil {
		// store.Val is v, converted for assignability.
		b.emitDebugRef(a.expr, store.Val, false)
	}
}

func (a *address) address(b *builder) Value {
	if a.expr != nil {
		b.emitDebugRef(a.expr, a.addr, true)
	}
	return a.addr
}

func (a *address) typ() Type {
	return ssaDeref(a.addr.Type())
}

// An element is an lvalue represented by m[k], the location of an
// element of a map or string.  These locations are not addressable
// since pointers cannot be formed from them, but they do support
// load(), and in the case of maps, store().
//
type element struct {
	m, k Value // map or string
	t    Type  // map element type or string byte type
	pos  Pos   // source position of colon ({k:v}) or lbrack (m[k]=v)
}

func (e *element) load(b *builder) Value {
	l := &Lookup{
		X:     e.m,
		Index: e.k,
	}
	l.setPos(e.pos)
	l.setType(e.t)
	return b.emit(l)
}

func (e *element) store(b *builder, v Value) {
	up := &MapUpdate{
		Map:   e.m,
		Key:   e.k,
		Value: b.emitConv(v, e.t),
	}
	up.pos = e.pos
	b.emit(up)
}

func (e *element) address(b *builder) Value {
	panic("map/string elements are not addressable")
}

func (e *element) typ() Type {
	return e.t
}

// A blank is a dummy variable whose name is "_".
// It is not reified: loads are illegal and stores are ignored.
//
type blank struct{}

func (bl blank) load(b *builder) Value {
	panic("blank.load is illegal")
}

func (bl blank) store(b *builder, v Value) {
	// no-op
}

func (bl blank) address(b *builder) Value {
	panic("blank var is not addressable")
}

func (bl blank) typ() Type {
	// This should be the type of the blank Ident; the typechecker
	// doesn't provide this yet, but fortunately, we don't need it
	// yet either.
	panic("blank.typ is unimplemented")
}
