// Copyright 2013 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssautil

import "github.com/despiteallobjections/amigo/types"

// This file defines utilities for visiting the SSA representation of
// a Program.
//
// TODO(adonovan): test coverage.

// AllFunctions finds and returns the set of functions potentially
// needed by program prog, as determined by a simple linker-style
// reachability algorithm starting from the members and method-sets of
// each package.  The result may include anonymous functions and
// synthetic wrappers.
//
// Precondition: all packages are built.
//
func AllFunctions(prog *types.Program) map[*types.Function]bool {
	visit := visitor{
		prog: prog,
		seen: make(map[*types.Function]bool),
	}
	visit.program()
	return visit.seen
}

type visitor struct {
	prog *types.Program
	seen map[*types.Function]bool
}

func (visit *visitor) program() {
	for _, pkg := range visit.prog.AllPackages() {
		for _, mem := range pkg.Members {
			if fn, ok := mem.(*types.Function); ok {
				visit.function(fn)
			}
		}
	}
	for _, T := range visit.prog.RuntimeTypes() {
		mset := visit.prog.MethodSets.MethodSet(T)
		for i, n := 0, mset.Len(); i < n; i++ {
			visit.function(visit.prog.MethodValue(mset.At(i)))
		}
	}
}

func (visit *visitor) function(fn *types.Function) {
	if !visit.seen[fn] {
		visit.seen[fn] = true
		var buf [10]*types.Value // avoid alloc in common case
		for _, b := range fn.Blocks {
			for _, instr := range b.Instrs {
				for _, op := range instr.Operands(buf[:0]) {
					if fn, ok := (*op).(*types.Function); ok {
						visit.function(fn)
					}
				}
			}
		}
	}
}

// MainPackages returns the subset of the specified packages
// named "main" that define a main function.
// The result may include synthetic "testmain" packages.
func MainPackages(pkgs []*types.SSAPackage) []*types.SSAPackage {
	var mains []*types.SSAPackage
	for _, pkg := range pkgs {
		if pkg.Pkg.Name() == "main" && pkg.Func("main") != nil {
			mains = append(mains, pkg)
		}
	}
	return mains
}
