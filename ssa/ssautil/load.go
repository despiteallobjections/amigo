// Copyright 2015 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssautil

// This file defines utility functions for constructing programs in SSA form.

import (
	"golang.org/x/tools/go/packages"

	"github.com/mdempsky/amigo/loader"
	"github.com/mdempsky/amigo/ssa"
	"github.com/mdempsky/amigo/syntax"
	"github.com/mdempsky/amigo/types"
)

// Packages creates an SSA program for a set of packages.
//
// The packages must have been loaded from source syntax using the
// golang.org/x/tools/go/packages.Load function in LoadSyntax or
// LoadAllSyntax mode.
//
// Packages creates an SSA package for each well-typed package in the
// initial list, plus all their dependencies. The resulting list of
// packages corresponds to the list of initial packages, and may contain
// a nil if SSA code could not be constructed for the corresponding initial
// package due to type errors.
//
// Code for bodies of functions is not built until Build is called on
// the resulting Program. SSA code is constructed only for the initial
// packages with well-typed syntax trees.
//
// The mode parameter controls diagnostics and checking during SSA construction.
//
func Packages(initial []*packages.Package, mode ssa.BuilderMode) (*ssa.Program, []*ssa.SSAPackage) {
	return doPackages(initial, mode, false)
}

// AllPackages creates an SSA program for a set of packages plus all
// their dependencies.
//
// The packages must have been loaded from source syntax using the
// golang.org/x/tools/go/packages.Load function in LoadAllSyntax mode.
//
// AllPackages creates an SSA package for each well-typed package in the
// initial list, plus all their dependencies. The resulting list of
// packages corresponds to the list of initial packages, and may contain
// a nil if SSA code could not be constructed for the corresponding
// initial package due to type errors.
//
// Code for bodies of functions is not built until Build is called on
// the resulting Program. SSA code is constructed for all packages with
// well-typed syntax trees.
//
// The mode parameter controls diagnostics and checking during SSA construction.
//
func AllPackages(initial []*packages.Package, mode ssa.BuilderMode) (*ssa.Program, []*ssa.SSAPackage) {
	return doPackages(initial, mode, true)
}

func doPackages(initial []*packages.Package, mode ssa.BuilderMode, deps bool) (*ssa.Program, []*ssa.SSAPackage) {

	prog := ssa.NewProgram(mode)

	isInitial := make(map[*packages.Package]bool, len(initial))
	for _, p := range initial {
		isInitial[p] = true
	}

	ssamap := make(map[*packages.Package]*ssa.SSAPackage)
	packages.Visit(initial, nil, func(p *packages.Package) {
		panic("TODO: need to manually parse and type check packages ourselves")
		/*
			if p.Types != nil && !p.IllTyped {
				var files []*syntax.File
				if deps || isInitial[p] {
					files = p.Syntax
				}
				ssamap[p] = prog.CreatePackage(p.Types, files, p.TypesInfo, true)
			}
		*/
	})

	var ssapkgs []*ssa.SSAPackage
	for _, p := range initial {
		ssapkgs = append(ssapkgs, ssamap[p]) // may be nil
	}
	return prog, ssapkgs
}

// CreateProgram returns a new program in SSA form, given a program
// loaded from source.  An SSA package is created for each transitively
// error-free package of lprog.
//
// Code for bodies of functions is not built until Build is called
// on the result.
//
// The mode parameter controls diagnostics and checking during SSA construction.
//
// Deprecated: Use golang.org/x/tools/go/packages and the Packages
// function instead; see ssa.ExampleLoadPackages.
//
func CreateProgram(lprog *loader.Program, mode ssa.BuilderMode) *ssa.Program {
	prog := ssa.NewProgram(mode)

	for _, info := range lprog.AllPackages {
		if info.TransitivelyErrorFree {
			prog.CreatePackage(info.Pkg, info.Files, &info.Info, info.Importable)
		}
	}

	return prog
}

// BuildPackage builds an SSA program with IR for a single package.
//
// It populates pkg by type-checking the specified file ASTs.  All
// dependencies are loaded using the importer specified by tc, which
// typically loads compiler export data; SSA code cannot be built for
// those packages.  BuildPackage then constructs an ssa.Program with all
// dependency packages created, and builds and returns the SSA package
// corresponding to pkg.
//
// The caller must have set pkg.Path() to the import path.
//
// The operation fails if there were any type-checking or import errors.
//
// See ../example_test.go for an example.
//
func BuildPackage(tc *types.Config, pkg *types.Package, files []*syntax.File, mode ssa.BuilderMode) (*ssa.SSAPackage, *types.Info, error) {
	if pkg.Path() == "" {
		panic("package has no import path")
	}

	info := &types.Info{
		Types:      make(map[syntax.Expr]types.TypeAndValue),
		Defs:       make(map[*syntax.Name]types.Object),
		Uses:       make(map[*syntax.Name]types.Object),
		Implicits:  make(map[syntax.Node]types.Object),
		Scopes:     make(map[syntax.Node]*types.Scope),
		Selections: make(map[*syntax.SelectorExpr]*types.Selection),
	}
	if err := types.NewChecker(tc, pkg, info).Files(files); err != nil {
		return nil, nil, err
	}

	prog := ssa.NewProgram(mode)

	// Create SSA packages for all imports.
	// Order is not significant.
	created := make(map[*types.Package]bool)
	var createAll func(pkgs []*types.Package)
	createAll = func(pkgs []*types.Package) {
		for _, p := range pkgs {
			if !created[p] {
				created[p] = true
				prog.CreatePackage(p, nil, nil, true)
				createAll(p.Imports())
			}
		}
	}
	createAll(pkg.Imports())

	// Create and build the primary package.
	ssapkg := prog.CreatePackage(pkg, files, info, false)
	ssapkg.Build()
	return ssapkg, info, nil
}
