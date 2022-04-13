// Copyright 2022 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package types

import (
	"fmt"
	"go/constant"

	. "github.com/despiteallobjections/amigo/syntax"
)

// This file implements amigo's "writer" logic. The idea is to
// serialize a compact description of the input, so that the "reader"
// can construct appropriate data structures.
//
// For now, we simply serialize into an anyBuffer. Longer term, the
// serialization should produce a portable byte serialization.

type writer struct {
	buf  *anyBuffer
	info *Info
}

// TODO(mdempsky): Implement more fleshed out sync scheme, like unified IR.
func (w *writer) sync() { w.buf.WriteAny(nil) }

func (w *writer) bool(b bool) bool { w.buf.WriteAny(b); return b }
func (w *writer) int(x int)        { w.buf.WriteAny(x) }
func (w *writer) int64(x int64)    { w.buf.WriteAny(x) }
func (w *writer) string(s string)  { w.buf.WriteAny(s) }

func (w *writer) op(op Operator)         { w.buf.WriteAny(op) }
func (w *writer) tok(tok Token)          { w.buf.WriteAny(tok) }
func (w *writer) pos(pos Pos)            { w.buf.WriteAny(pos) }
func (w *writer) val(val constant.Value) { w.buf.WriteAny(val) }
func (w *writer) typ(typ Type)           { w.buf.WriteAny(typ) }
func (w *writer) obj(obj Object)         { w.buf.WriteAny(obj) }
func (w *writer) exprTODO(expr Expr)     { w.buf.WriteAny(expr) }

func (w *writer) addLocal(typ Type, pos Pos) {
	w.sync()
	w.typ(typ)
	w.pos(pos)
}

func (w *writer) labelledBlock(label *Label) {
	w.sync()
	w.int(label.index)
	w.string(label.Name())
}

func (w *writer) useLabel(name *Name) {
	if w.bool(name == nil) {
		return
	}
	label := w.info.Uses[name].(*Label)
	w.labelledBlock(label)
}

func (w *writer) emitDebugRef(e Expr, isAddr bool) {
	if e == nil {
		panic("nil")
	}

	var obj Object
	e = Unparen(e)
	if id, ok := e.(*Name); ok {
		if isBlankIdent(id) {
			w.bool(false)
			return
		}
		obj = w.objectOf(id)
		switch obj.(type) {
		case *Nil, *Const, *Builtin:
			w.bool(false)
			return
		}
	}

	w.bool(true)
	w.exprTODO(e)
	w.bool(isAddr)
	if w.bool(obj != nil) {
		w.obj(obj)
	}
}

// Like ObjectOf, but panics instead of returning nil.
// Only valid during p's create and build phases.
func (w *writer) objectOf(id *Name) Object {
	if o := w.info.ObjectOf(id); o != nil {
		return o
	}
	panic(fmt.Sprintf("no types.Object for syntax.Name %s @ %s",
		id.Value, id.Pos()))
}

// Like TypeOf, but panics instead of returning nil.
// Only valid during p's create and build phases.
func (w *writer) typeOf(e Expr) Type {
	if T := w.info.TypeOf(e); T != nil {
		return T
	}
	panic(fmt.Sprintf("no type for %T @ %s",
		e, e.Pos()))
}

func (w *writer) int64Of(e Expr) int64 {
	tv, ok := w.info.Types[e]
	assert(ok)
	x, ok := constant.Int64Val(tv.Value)
	assert(ok)
	return x
}
