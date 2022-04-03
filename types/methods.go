// Copyright 2013 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package types

// This file defines utilities for population of method sets.

import (
	"fmt"
)

// MethodValue returns the Function implementing method sel, building
// wrapper methods on demand.  It returns nil if sel denotes an
// abstract (interface) method.
//
// Precondition: sel.Kind() == MethodVal.
//
// Thread-safe.
//
// EXCLUSIVE_LOCKS_ACQUIRED(prog.methodsMu)
//
func (prog *Program) MethodValue(sel *Selection) *Function {
	if sel.Kind() != MethodVal {
		panic(fmt.Sprintf("MethodValue(%s) kind != MethodVal", sel))
	}
	T := sel.Recv()
	if isInterface(T) {
		return nil // abstract method
	}
	if prog.mode&LogSource != 0 {
		defer logStack("MethodValue %s %v", T, sel)()
	}

	prog.methodsMu.Lock()
	defer prog.methodsMu.Unlock()

	return prog.addMethod(prog.createMethodSet(T), sel)
}

// LookupMethod returns the implementation of the method of type T
// identified by (pkg, name).  It returns nil if the method exists but
// is abstract, and panics if T has no such method.
//
func (prog *Program) LookupMethod(T Type, pkg *Package, name string) *Function {
	sel := prog.MethodSets.MethodSet(T).Lookup(pkg, name)
	if sel == nil {
		panic(fmt.Sprintf("%s has no method %s", T, Id(pkg, name)))
	}
	return prog.MethodValue(sel)
}

// ssaMethodSet contains the (concrete) methods of a non-interface type.
type ssaMethodSet struct {
	mapping  map[string]*Function // populated lazily
	complete bool                 // mapping contains all methods
}

// Precondition: !isInterface(T).
// EXCLUSIVE_LOCKS_REQUIRED(prog.methodsMu)
func (prog *Program) createMethodSet(T Type) *ssaMethodSet {
	mset, ok := prog.methodSets.At(T).(*ssaMethodSet)
	if !ok {
		mset = &ssaMethodSet{mapping: make(map[string]*Function)}
		prog.methodSets.Set(T, mset)
	}
	return mset
}

// EXCLUSIVE_LOCKS_REQUIRED(prog.methodsMu)
func (prog *Program) addMethod(mset *ssaMethodSet, sel *Selection) *Function {
	if sel.Kind() == MethodExpr {
		panic(sel)
	}
	id := sel.Obj().Id()
	fn := mset.mapping[id]
	if fn == nil {
		obj := sel.Obj().(*Func)

		needsPromotion := len(sel.Index()) > 1
		needsIndirection := !isPointer(recvType(obj)) && isPointer(sel.Recv())
		if needsPromotion || needsIndirection {
			fn = prog.makeWrapper(sel)
		} else {
			fn = prog.declaredFunc(obj)
		}
		if fn.Signature.Recv() == nil {
			panic(fn) // missing receiver
		}
		mset.mapping[id] = fn
	}
	return fn
}

// RuntimeTypes returns a new unordered slice containing all
// concrete types in the program for which a complete (non-empty)
// method set is required at run-time.
//
// Thread-safe.
//
// EXCLUSIVE_LOCKS_ACQUIRED(prog.methodsMu)
//
func (prog *Program) RuntimeTypes() []Type {
	prog.methodsMu.Lock()
	defer prog.methodsMu.Unlock()

	var res []Type
	prog.methodSets.Iterate(func(T Type, v interface{}) {
		if v.(*ssaMethodSet).complete {
			res = append(res, T)
		}
	})
	return res
}

// declaredFunc returns the concrete function/method denoted by obj.
// Panic ensues if there is none.
//
func (prog *Program) declaredFunc(obj *Func) *Function {
	if v := prog.packageLevelValue(obj); v != nil {
		return v.(*Function)
	}
	panic("no concrete method: " + obj.String())
}

// needMethodsOf ensures that runtime type information (including the
// complete method set) is available for the specified type T and all
// its subcomponents.
//
// needMethodsOf must be called for at least every type that is an
// operand of some MakeInterface instruction, and for the type of
// every exported package member.
//
// Precondition: T is not a method signature (*Signature with Recv()!=nil).
//
// Thread-safe.  (Called via emitConv from multiple builder goroutines.)
//
// TODO(adonovan): make this faster.  It accounts for 20% of SSA build time.
//
// EXCLUSIVE_LOCKS_ACQUIRED(prog.methodsMu)
//
func (prog *Program) needMethodsOf(T Type) {
	prog.methodsMu.Lock()
	prog.needMethods(T, false)
	prog.methodsMu.Unlock()
}

// Precondition: T is not a method signature (*Signature with Recv()!=nil).
// Recursive case: skip => don't create methods for T.
//
// EXCLUSIVE_LOCKS_REQUIRED(prog.methodsMu)
//
func (prog *Program) needMethods(T Type, skip bool) {
	// Each package maintains its own set of types it has visited.
	if prevSkip, ok := prog.runtimeTypes.At(T).(bool); ok {
		// needMethods(T) was previously called
		if !prevSkip || skip {
			return // already seen, with same or false 'skip' value
		}
	}
	prog.runtimeTypes.Set(T, skip)

	tmset := prog.MethodSets.MethodSet(T)

	if !skip && !isInterface(T) && tmset.Len() > 0 {
		// Create methods of T.
		mset := prog.createMethodSet(T)
		if !mset.complete {
			mset.complete = true
			n := tmset.Len()
			for i := 0; i < n; i++ {
				prog.addMethod(mset, tmset.At(i))
			}
		}
	}

	// Recursion over signatures of each method.
	for i := 0; i < tmset.Len(); i++ {
		sig := tmset.At(i).Type().(*Signature)
		prog.needMethods(sig.Params(), false)
		prog.needMethods(sig.Results(), false)
	}

	switch t := T.(type) {
	case *Basic:
		// nop

	case *Interface, *TypeParam:
		// nop---handled by recursion over method set.

	case *Pointer:
		prog.needMethods(t.Elem(), false)

	case *Slice:
		prog.needMethods(t.Elem(), false)

	case *Chan:
		prog.needMethods(t.Elem(), false)

	case *Map:
		prog.needMethods(t.Key(), false)
		prog.needMethods(t.Elem(), false)

	case *Signature:
		if t.Recv() != nil {
			panic(fmt.Sprintf("Signature %s has Recv %s", t, t.Recv()))
		}
		prog.needMethods(t.Params(), false)
		prog.needMethods(t.Results(), false)

	case *Named:
		// A pointer-to-named type can be derived from a named
		// type via reflection.  It may have methods too.
		prog.needMethods(NewPointer(T), false)

		// Consider 'type T struct{S}' where S has methods.
		// Reflection provides no way to get from T to struct{S},
		// only to S, so the method set of struct{S} is unwanted,
		// so set 'skip' flag during recursion.
		prog.needMethods(t.Underlying(), true)

	case *Array:
		prog.needMethods(t.Elem(), false)

	case *Struct:
		for i, n := 0, t.NumFields(); i < n; i++ {
			prog.needMethods(t.Field(i).Type(), false)
		}

	case *Tuple:
		for i, n := 0, t.Len(); i < n; i++ {
			prog.needMethods(t.At(i).Type(), false)
		}

	default:
		panic(T)
	}
}
