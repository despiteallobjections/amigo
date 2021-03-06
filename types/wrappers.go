// Copyright 2013 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package types

// This file defines synthesis of Functions that delegate to declared
// methods; they come in three kinds:
//
// (1) wrappers: methods that wrap declared methods, performing
//     implicit pointer indirections and embedded field selections.
//
// (2) thunks: funcs that wrap declared methods.  Like wrappers,
//     thunks perform indirections and field selections. The thunk's
//     first parameter is used as the receiver for the method call.
//
// (3) bounds: funcs that wrap declared methods.  The bound's sole
//     free variable, supplied by a closure, is used as the receiver
//     for the method call.  No indirections or field selections are
//     performed since they can be done before the call.

import (
	"fmt"
	"strconv"
	"strings"
)

// -- wrappers -----------------------------------------------------------

// makeWrapper returns a synthetic method that delegates to the
// declared method denoted by meth.Obj(), first performing any
// necessary pointer indirections or field selections implied by meth.
//
// The resulting method's receiver type is meth.Recv().
//
// This function is versatile but quite subtle!  Consider the
// following axes of variation when making changes:
//   - optional receiver indirection
//   - optional implicit field selections
//   - meth.Obj() may denote a concrete or an interface method
//   - the result may be a thunk or a wrapper.
//
// EXCLUSIVE_LOCKS_REQUIRED(prog.methodsMu)
//
func (prog *Program) makeWrapper(sel *Selection) *Function {
	return prog.makeWrapperKey(sel.asKey())
}

func (prog *Program) makeWrapperKey(key selectionKey) *Function {
	obj := key.obj.(*Func) // the declared function
	objSig := obj.Type().(*Signature)
	objRecv := objSig.Recv()

	recv := NewVar(objRecv.Pos(), objRecv.Pkg(), objRecv.Name(), key.recv)

	var sig *Signature

	name := obj.Name()
	var description string
	var start int // first regular param
	if key.kind == MethodExpr {
		name += "$thunk"
		description = "thunk"
		start = 1

		params := []*Var{recv}
		for i := 0; i < objSig.Params().Len(); i++ {
			params = append(params, objSig.Params().At(i))
		}
		sig = NewSignatureType(nil, nil, nil, NewTuple(params...), objSig.Results(), objSig.Variadic())
	} else {
		description = "wrapper"
		sig = changeRecv(objSig, recv)
	}

	description = fmt.Sprintf("%s for %s", description, key.obj)
	if prog.mode&LogSource != 0 {
		defer logStack("make %s to (%s)", description, recv.Type())()
	}

	fn := &Function{
		name:            name,
		wrapperRecvType: key.recv,
		object:          obj,
		Signature:       sig,
		Synthetic:       description,
	}
	prog.build(fn, nil, func(b *builder) {
		b.addSpilledParam(recv)
		b.createParams(start)

		indices := key.indexSlice()

		var v Value = fn.Locals[0] // spilled receiver
		if isPointer(key.recv) {
			v = b.emitLoad(v)

			// For simple indirection wrappers, perform an informative nil-check:
			// "value method (T).f called using nil *T pointer"
			if len(indices) == 1 && !isPointer(recvType(obj)) {
				var c Call
				c.Call.Value = &SSABuiltin{
					name: "ssa:wrapnilchk",
					sig: NewSignatureType(nil, nil, nil,
						NewTuple(anonVar(key.recv), anonVar(tString), anonVar(tString)),
						NewTuple(anonVar(key.recv)), false),
				}
				c.Call.Args = []Value{
					v,
					stringConst(ssaDeref(key.recv).String()),
					stringConst(key.obj.Name()),
				}
				c.setType(v.Type())
				v = b.emit(&c)
			}
		}

		// Invariant: v is a pointer, either
		//   value of *A receiver param, or
		// address of  A spilled receiver.

		// We use pointer arithmetic (FieldAddr possibly followed by
		// Load) in preference to value extraction (Field possibly
		// preceded by Load).

		v = b.emitImplicitSelections(v, indices[:len(indices)-1])

		// Invariant: v is a pointer, either
		//   value of implicit *C field, or
		// address of implicit  C field.

		var c Call
		if r := recvType(obj); !isInterface(r) { // concrete method
			if !isPointer(r) {
				v = b.emitLoad(v)
			}
			c.Call.Value = prog.declaredFunc(obj)
			c.Call.Args = append(c.Call.Args, v)
		} else {
			c.Call.Method = obj
			c.Call.Value = b.emitLoad(v)
		}
		for _, arg := range fn.Params[1:] {
			c.Call.Args = append(c.Call.Args, arg)
		}
		b.emitTailCall(&c)
	})
	return fn
}

// createParams creates parameters for wrapper method fn based on its
// Signature.Params, which do not include the receiver.
// start is the index of the first regular parameter to use.
//
func (b *builder) createParams(start int) {
	tparams := b.Fn.Signature.Params()
	for i, n := start, tparams.Len(); i < n; i++ {
		b.Fn.addParamObj(tparams.At(i))
	}
}

// -- bounds -----------------------------------------------------------

// makeBound returns a bound method wrapper (or "bound"), a synthetic
// function that delegates to a concrete or interface method denoted
// by obj.  The resulting function has no receiver, but has one free
// variable which will be used as the method's receiver in the
// tail-call.
//
// Use MakeClosure with such a wrapper to construct a bound method
// closure.  e.g.:
//
//   type T int          or:  type T interface { meth() }
//   func (t T) meth()
//   var t T
//   f := t.meth
//   f() // calls t.meth()
//
// f is a closure of a synthetic wrapper defined as if by:
//
//   f := func() { return t.meth() }
//
// Unlike makeWrapper, makeBound need perform no indirection or field
// selections because that can be done before the closure is
// constructed.
//
// EXCLUSIVE_LOCKS_ACQUIRED(meth.Prog.methodsMu)
//
func (prog *Program) makeBound(obj *Func) *Function {
	sig := obj.Type().(*Signature)
	recv := sig.Recv()
	assert(recv != nil)

	prog.methodsMu.Lock()
	defer prog.methodsMu.Unlock()
	fn, ok := prog.bounds[obj]
	if !ok {
		description := fmt.Sprintf("bound method wrapper for %s", obj)
		if prog.mode&LogSource != 0 {
			defer logStack("%s", description)()
		}
		fn = &Function{
			name:      obj.Name() + "$bound",
			object:    obj,
			Signature: changeRecv(sig, nil), // drop receiver
			Synthetic: description,
		}
		prog.build(fn, nil, func(b *builder) {
			fv := &FreeVar{object: recv, typ: recv.Type(), parent: fn}
			fn.FreeVars = []*FreeVar{fv}
			b.createParams(0)
			var c Call

			if !isInterface(recvType(obj)) { // concrete
				c.Call.Value = prog.declaredFunc(obj)
				c.Call.Args = []Value{fv}
			} else {
				c.Call.Value = fv
				c.Call.Method = obj
			}
			for _, arg := range fn.Params {
				c.Call.Args = append(c.Call.Args, arg)
			}
			b.emitTailCall(&c)
		})

		prog.bounds[obj] = fn
	}
	return fn
}

// -- thunks -----------------------------------------------------------

// makeThunk returns a thunk, a synthetic function that delegates to a
// concrete or interface method denoted by sel.Obj().  The resulting
// function has no receiver, but has an additional (first) regular
// parameter.
//
// Precondition: sel.Kind() == types.MethodExpr.
//
//   type T int          or:  type T interface { meth() }
//   func (t T) meth()
//   f := T.meth
//   var t T
//   f(t) // calls t.meth()
//
// f is a synthetic wrapper defined as if by:
//
//   f := func(t T) { return t.meth() }
//
// TODO(adonovan): opt: currently the stub is created even when used
// directly in a function call: C.f(i, 0).  This is less efficient
// than inlining the stub.
//
// EXCLUSIVE_LOCKS_ACQUIRED(meth.Prog.methodsMu)
//
func (prog *Program) makeThunk(sel *Selection) *Function {
	if sel.Kind() != MethodExpr {
		panic(sel)
	}

	return prog.makeThunkKey(sel.asKey())
}

func (sel *Selection) asKey() selectionKey {
	return selectionKey{
		kind:     sel.Kind(),
		recv:     sel.Recv(),
		obj:      sel.Obj(),
		index:    fmt.Sprint(sel.Index()),
		indirect: sel.Indirect(),
	}
}

func (key selectionKey) indexSlice() []int {
	var res []int

	s := key.index
	s = strings.TrimPrefix(s, "[")
	s = strings.TrimSuffix(s, "]")

	for _, e := range strings.Split(s, " ") {
		n, err := strconv.Atoi(e)
		if err != nil {
			panic(err)
		}
		res = append(res, n)
	}
	return res
}

func (prog *Program) makeThunkKey(key selectionKey) *Function {
	prog.methodsMu.Lock()
	defer prog.methodsMu.Unlock()

	// Canonicalize key.recv to avoid constructing duplicate thunks.
	canonRecv, ok := prog.canon.At(key.recv).(Type)
	if !ok {
		canonRecv = key.recv
		prog.canon.Set(key.recv, canonRecv)
	}
	key.recv = canonRecv

	fn, ok := prog.thunks[key]
	if !ok {
		fn = prog.makeWrapperKey(key)
		if fn.Signature.Recv() != nil {
			panic(fn) // unexpected receiver
		}
		prog.thunks[key] = fn
	}
	return fn
}

func changeRecv(s *Signature, recv *Var) *Signature {
	return NewSignatureType(recv, nil, nil, s.Params(), s.Results(), s.Variadic())
}

// selectionKey is like types.Selection but a usable map key.
type selectionKey struct {
	kind     SelectionKind
	recv     Type // canonicalized via Program.canon
	obj      Object
	index    string
	indirect bool
}
