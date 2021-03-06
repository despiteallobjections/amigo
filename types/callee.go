// Copyright 2018 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package types

import (
	. "github.com/despiteallobjections/amigo/syntax"
)

// Callee returns the named target of a function call, if any:
// a function, method, builtin, or variable.
func Callee(info *Info, call *CallExpr) Object {
	var obj Object
	switch fun := Unparen(call.Fun).(type) {
	case *Name:
		obj = info.Uses[fun] // type, var, builtin, or declared func
	case *SelectorExpr:
		if sel, ok := info.Selections[fun]; ok {
			obj = sel.Obj() // method or field
		} else {
			obj = info.Uses[fun.Sel] // qualified identifier?
		}
	}
	if _, ok := obj.(*TypeName); ok {
		return nil // T(x) is a conversion, not a call
	}
	return obj
}

// StaticCallee returns the target (function or method) of a static
// function call, if any. It returns nil for calls to builtins.
func StaticCallee(info *Info, call *CallExpr) *Func {
	if f, ok := Callee(info, call).(*Func); ok && !interfaceMethod(f) {
		return f
	}
	return nil
}

func interfaceMethod(f *Func) bool {
	recv := f.Type().(*Signature).Recv()
	return recv != nil && IsInterface(recv.Type())
}
