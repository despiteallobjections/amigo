// Copyright 2022 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package types

import (
	"go/constant"

	. "github.com/despiteallobjections/amigo/syntax"
)

type reader struct {
	buf *anyBuffer
	b   *builder
}

func (r *reader) sync() { assert(r.buf.ReadAny() == nil) }

func (r *reader) bool() bool     { return r.buf.ReadAny().(bool) }
func (r *reader) int() int       { return r.buf.ReadAny().(int) }
func (r *reader) int64() int64   { return r.buf.ReadAny().(int64) }
func (r *reader) string() string { return r.buf.ReadAny().(string) }

func (r *reader) op() Operator        { return r.buf.ReadAny().(Operator) }
func (r *reader) tok() Token          { return r.buf.ReadAny().(Token) }
func (r *reader) pos() Pos            { return r.buf.ReadAny().(Pos) }
func (r *reader) val() constant.Value { return r.buf.ReadAny().(constant.Value) }
func (r *reader) typ() Type           { return r.buf.ReadAny().(Type) }
func (r *reader) obj() Object         { return r.buf.ReadAny().(Object) }
func (r *reader) exprTODO() Expr      { return r.buf.ReadAny().(Expr) }

func (r *reader) addLocal() *Alloc {
	r.sync()
	typ := r.typ()
	pos := r.pos()

	b := r.b
	fn := b.Fn
	v := &Alloc{}
	v.setType(NewPointer(typ))
	v.setPos(pos)
	fn.Locals = append(fn.Locals, v)
	b.emit(v)
	return v
}

func (r *reader) labelledBlock() *lblock {
	r.sync()
	index := r.int()
	name := r.string()

	b := r.b
	lb := &b.lblocks[index]
	if lb._goto == nil {
		lb._goto = b.newBasicBlock(name)
	}
	return lb
}

func (r *reader) useLabel() *lblock {
	if r.bool() {
		return &r.b.implicit
	}
	return r.labelledBlock()
}

func (r *reader) emitDebugRef(v Value) {
	if v == nil {
		panic("nil")
	}

	if !r.bool() {
		return // blank, const, or predeclared
	}

	e := r.exprTODO()
	isAddr := r.bool()
	var obj Object
	if r.bool() {
		obj = r.obj()
	}

	if !r.b.debugInfo() {
		// TODO(mdempsky): Allow skipping reading the expr/obj
		// entirely in this case?
		return // debugging not enabled
	}
	r.b.emit(&DebugRef{
		X:      v,
		Expr:   e,
		IsAddr: isAddr,
		object: obj,
	})
}
