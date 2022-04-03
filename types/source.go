// Copyright 2013 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package types

import . "github.com/mdempsky/amigo/syntax"

// This file defines utilities for working with source positions
// or source-level named entities ("objects").

// TODO(adonovan): test that {Value,Instruction}.Pos() positions match
// the originating syntax, as specified.

// --- Lookup functions for source-level named entities (types.Objects) ---

// Package returns the SSA Package corresponding to the specified
// type-checker package object.
// It returns nil if no such SSA package has been created.
//
func (prog *Program) Package(obj *Package) *SSAPackage {
	return prog.packages[obj]
}

// packageLevelValue returns the package-level value corresponding to
// the specified named object, which may be a package-level const
// (*Const), var (*Global) or func (*Function) of some package in
// prog.  It returns nil if the object is not found.
//
func (prog *Program) packageLevelValue(obj Object) Value {
	if pkg := prog.Package(obj.Pkg()); pkg != nil {
		return pkg.values[obj]
	}
	return nil
}

// tokenPos returns n.Pos().
//
// It exists just for internal documentation purposes, to help remind
// which token position package ssa was originally accessing.
func tokenPos(n Node, which string) Pos { return n.Pos() }
