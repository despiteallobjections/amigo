// Copyright 2018 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package typeutil

import (
	"github.com/mdempsky/amigo/syntax"
	"github.com/mdempsky/amigo/types"
)

// Callee returns the named target of a function call, if any:
// a function, method, builtin, or variable.
func Callee(info *types.Info, call *syntax.CallExpr) types.Object {
	var obj types.Object
	switch fun := syntax.Unparen(call.Fun).(type) {
	case *syntax.Name:
		obj = info.Uses[fun] // type, var, builtin, or declared func
	case *syntax.SelectorExpr:
		if sel, ok := info.Selections[fun]; ok {
			obj = sel.Obj() // method or field
		} else {
			obj = info.Uses[fun.Sel] // qualified identifier?
		}
	}
	if _, ok := obj.(*types.TypeName); ok {
		return nil // T(x) is a conversion, not a call
	}
	return obj
}

// StaticCallee returns the target (function or method) of a static
// function call, if any. It returns nil for calls to builtins.
func StaticCallee(info *types.Info, call *syntax.CallExpr) *types.Func {
	if f, ok := Callee(info, call).(*types.Func); ok && !interfaceMethod(f) {
		return f
	}
	return nil
}

func interfaceMethod(f *types.Func) bool {
	recv := f.Type().(*types.Signature).Recv()
	return recv != nil && types.IsInterface(recv.Type())
}
