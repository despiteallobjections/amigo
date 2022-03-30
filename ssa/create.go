// Copyright 2013 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssa

// This file implements the CREATE phase of SSA construction.
// See builder.go for explanation.

import (
	"fmt"
	"os"
	"sync"

	. "github.com/mdempsky/amigo/syntax"
	. "github.com/mdempsky/amigo/types"
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
func memberFromObject(pkg *SSAPackage, obj Object, syntax Node) {
	name := obj.Name()
	switch obj := obj.(type) {
	case *Builtin:
		if pkg.Pkg != Unsafe {
			panic("unexpected builtin object: " + obj.String())
		}

	case *TypeName:
		pkg.Members[name] = &SSAType{
			object: obj,
			pkg:    pkg,
		}

	case *Const:
		c := &NamedConst{
			object: obj,
			Value:  NewSSAConst(obj.Val(), obj.Type()),
			pkg:    pkg,
		}
		pkg.values[obj] = c.Value
		pkg.Members[name] = c

	case *Var:
		g := &Global{
			Pkg:    pkg,
			name:   name,
			object: obj,
			typ:    NewPointer(obj.Type()), // address
			pos:    obj.Pos(),
		}
		pkg.values[obj] = g
		pkg.Members[name] = g

	case *Func:
		sig := obj.Type().(*Signature)
		if sig.Recv() == nil && name == "init" {
			pkg.ninit++
			name = fmt.Sprintf("init#%d", pkg.ninit)
		}
		fn := &Function{
			name:      name,
			object:    obj,
			Signature: sig,
			syntax:    syntax,
			pos:       obj.Pos(),
			Pkg:       pkg,
			Prog:      pkg.Prog,
		}
		if syntax == nil {
			fn.Synthetic = "loaded from gc object file"
		}

		pkg.values[obj] = fn
		if sig.Recv() == nil {
			pkg.Members[name] = fn // package-level function
		}

	default: // (incl. *types.Package)
		panic("unexpected Object type: " + obj.String())
	}
}

// membersFromDecl populates package pkg with members for each
// typechecker object (var, func, const or type) associated with the
// specified decl.
//
func membersFromDecl(pkg *SSAPackage, decl Decl) {
	switch decl := decl.(type) {
	case *GenDecl:
		for _, spec := range decl.SpecList {
			switch spec := spec.(type) {
			case *ConstSpec:
				for _, id := range spec.NameList {
					if !isBlankIdent(id) {
						memberFromObject(pkg, pkg.info.Defs[id], nil)
					}
				}

			case *VarSpec:
				for _, id := range spec.NameList {
					if !isBlankIdent(id) {
						memberFromObject(pkg, pkg.info.Defs[id], decl)
					}
				}

			case *TypeSpec:
				id := spec.Name
				if !isBlankIdent(id) {
					memberFromObject(pkg, pkg.info.Defs[id], nil)
				}
			}
		}

	case *FuncDecl:
		id := decl.Name
		if !isBlankIdent(id) {
			memberFromObject(pkg, pkg.info.Defs[id], decl)
		}
	}
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
		Prog:    prog,
		Members: make(map[string]Member),
		values:  make(map[Object]Value),
		Pkg:     pkg,
		info:    info,  // transient (CREATE and BUILD phases)
		files:   files, // transient (CREATE and BUILD phases)
	}

	// Add init() function.
	p.init = &Function{
		name:      "init",
		Signature: new(Signature),
		Synthetic: "package initializer",
		Pkg:       p,
		Prog:      prog,
	}
	p.Members[p.init.name] = p.init

	// CREATE phase.
	// Allocate all package members: vars, funcs, consts and types.
	if len(files) > 0 {
		// Go source package.
		for _, file := range files {
			for _, decl := range file.DeclList {
				membersFromDecl(p, decl)
			}
		}
	} else {
		// GC-compiled binary package (or "unsafe")
		// No code.
		// No position information.
		scope := p.Pkg.Scope()
		for _, name := range scope.Names() {
			obj := scope.Lookup(name)
			memberFromObject(p, obj, nil)
			if obj, ok := obj.(*TypeName); ok {
				if named, ok := obj.Type().(*Named); ok {
					for i, n := 0, named.NumMethods(); i < n; i++ {
						memberFromObject(p, named.Method(i), nil)
					}
				}
			}
		}
	}

	if prog.mode&BareInits == 0 {
		// Add initializer guard variable.
		initguard := &Global{
			Pkg:  p,
			name: "init$guard",
			typ:  NewPointer(tBool),
		}
		p.Members[initguard.Name()] = initguard
	}

	if prog.mode&GlobalDebug != 0 {
		p.SetDebugMode(true)
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
