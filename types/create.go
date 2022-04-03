// Copyright 2013 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package types

// This file implements the CREATE phase of SSA construction.
// See builder.go for explanation.

import (
	"fmt"
	"os"
	"sync"

	. "github.com/mdempsky/amigo/syntax"
)

// NewProgram returns a new SSA Program.
//
// mode controls diagnostics and checking during SSA construction.
//
func NewProgram(mode BuilderMode) *Program {
	prog := &Program{
		imported: make(map[string]*SSAPackage),
		packages: make(map[*Package]*SSAPackage),
		thunks:   make(map[selectionKey]*Function),
		bounds:   make(map[*Func]*Function),
		mode:     mode,
	}

	h := MakeHasher() // protected by methodsMu, in effect
	prog.methodSets.SetHasher(h)
	prog.canon.SetHasher(h)

	return prog
}

// memberFromObject populates package pkg with a member for the
// typechecker object obj.
//
// For objects from Go source code, syntax is the associated syntax
// tree (for funcs and vars only); it will be used during the build
// phase.
//
func memberFromFunc(pkg *SSAPackage, obj *Func) *Function {
	name := obj.Name()
	sig := obj.Type().(*Signature)
	if sig.Recv() == nil && name == "init" {
		ninit := 0
		for obj.Pkg().inits[ninit] != obj {
			ninit++
		}
		name = fmt.Sprintf("init#%d", 1+ninit)
	}
	fn := &Function{
		name:      name,
		object:    obj,
		Signature: sig,
		Pkg:       pkg,
	}
	if pkg.info == nil {
		fn.Synthetic = "loaded from gc object file"
	}

	pkg.values[obj] = fn
	if sig.Recv() == nil {
		pkg.Members[name] = fn // package-level function
	}
	return fn
}

func memberFromVar(pkg *SSAPackage, obj *Var) *Global {
	g := &Global{
		object: obj,
		typ:    NewPointer(obj.Type()), // address
	}
	pkg.values[obj] = g
	pkg.Members[obj.Name()] = g
	return g
}

// CreatePackage constructs and returns an SSA Package from the
// specified type-checked, error-free file ASTs, and populates its
// Members mapping.
//
// importable determines whether this package should be returned by a
// subsequent call to ImportedPackage(pkg.Path()).
//
// The real work of building SSA form for each function is not done
// until a subsequent call to Package.Build().
//
func (prog *Program) CreatePackage(pkg *Package, files []*File, info *Info, importable bool) *SSAPackage {
	p := &SSAPackage{
		Pkg:     pkg,
		Members: make(map[string]Member),
		values:  make(map[Object]Value),
		info:    info, // transient (CREATE and BUILD phases)
	}

	// Add init() function.
	obj := NewFunc(NoPos, pkg, "init", new(Signature))
	fn := &Function{
		name:      obj.Name(),
		object:    obj,
		Signature: obj.Type().(*Signature),
		Synthetic: "package initializer",
		Pkg:       p,
	}
	p.InitFunc = fn
	p.Members[fn.name] = fn

	// CREATE phase.
	// Allocate all package members: vars, funcs, consts and types.

	for _, init := range p.Pkg.inits {
		memberFromFunc(p, init)
	}

	scope := p.Pkg.Scope()
	for _, name := range scope.Names() {
		switch obj := scope.Lookup(name).(type) {
		case *Func:
			memberFromFunc(p, obj)
		case *TypeName:
			if !obj.IsAlias() {
				if named, ok := obj.Type().(*Named); ok {
					for i, n := 0, named.NumMethods(); i < n; i++ {
						memberFromFunc(p, named.Method(i))
					}
				}
			}
		case *Var:
			memberFromVar(p, obj)
		}
	}

	if prog.mode&BareInits == 0 {
		// Add initializer guard variable.
		initGuard := NewVar(NoPos, pkg, "init$guard", tBool)
		p.InitGuard = memberFromVar(p, initGuard)
	}

	if prog.mode&PrintPackages != 0 {
		printMu.Lock()
		p.WriteTo(os.Stdout)
		printMu.Unlock()
	}

	if importable {
		prog.imported[p.Pkg.Path()] = p
	}
	prog.packages[p.Pkg] = p

	return p
}

// printMu serializes printing of Packages/Functions to stdout.
var printMu sync.Mutex

// AllPackages returns a new slice containing all packages in the
// program prog in unspecified order.
//
func (prog *Program) AllPackages() []*SSAPackage {
	pkgs := make([]*SSAPackage, 0, len(prog.packages))
	for _, pkg := range prog.packages {
		pkgs = append(pkgs, pkg)
	}
	return pkgs
}

// ImportedPackage returns the importable Package whose PkgPath
// is path, or nil if no such Package has been created.
//
// A parameter to CreatePackage determines whether a package should be
// considered importable. For example, no import declaration can resolve
// to the ad-hoc main package created by 'go build foo.go'.
//
// TODO(adonovan): rethink this function and the "importable" concept;
// most packages are importable. This function assumes that all
// types.Package.Path values are unique within the ssa.Program, which is
// false---yet this function remains very convenient.
// Clients should use (*Program).Package instead where possible.
// SSA doesn't really need a string-keyed map of packages.
//
func (prog *Program) ImportedPackage(path string) *SSAPackage {
	return prog.imported[path]
}
