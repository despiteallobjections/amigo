// Copyright 2014 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package types

// This file defines utilities for user interfaces that display types.

// IntuitiveMethodSet returns the intuitive method set of a type T,
// which is the set of methods you can call on an addressable value of
// that type.
//
// The result always contains MethodSet(T), and is exactly MethodSet(T)
// for interface types and for pointer-to-concrete types.
// For all other concrete types T, the result additionally
// contains each method belonging to *T if there is no identically
// named method on T itself.
//
// This corresponds to user intuition about method sets;
// this function is intended only for user interfaces.
//
// The order of the result is as for types.MethodSet(T).
//
func IntuitiveMethodSet(T Type, msets *MethodSetCache) []*Selection {
	isPointerToConcrete := func(T Type) bool {
		ptr, ok := T.(*Pointer)
		return ok && !IsInterface(ptr.Elem())
	}

	var result []*Selection
	mset := msets.MethodSet(T)
	if IsInterface(T) || isPointerToConcrete(T) {
		for i, n := 0, mset.Len(); i < n; i++ {
			result = append(result, mset.At(i))
		}
	} else {
		// T is some other concrete type.
		// Report methods of T and *T, preferring those of T.
		pmset := msets.MethodSet(NewPointer(T))
		for i, n := 0, pmset.Len(); i < n; i++ {
			meth := pmset.At(i)
			if m := mset.Lookup(meth.Obj().Pkg(), meth.Obj().Name()); m != nil {
				meth = m
			}
			result = append(result, meth)
		}

	}
	return result
}
