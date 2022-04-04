// Copyright 2022 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package types

import . "github.com/mdempsky/amigo/syntax"

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
func (w *writer) string(s string)  { w.buf.WriteAny(s) }

func (w *writer) op(op Operator) { w.buf.WriteAny(op) }
func (w *writer) pos(pos Pos)    { w.buf.WriteAny(pos) }
func (w *writer) typ(typ Type)   { w.buf.WriteAny(typ) }
func (w *writer) obj(obj Object) { w.buf.WriteAny(obj) }

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
