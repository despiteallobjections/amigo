// Copyright 2015 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssautil

// This file defines utility functions for constructing programs in SSA form.

import (
	"fmt"

	"golang.org/x/tools/go/packages"

	"github.com/despiteallobjections/amigo/loader"
	"github.com/despiteallobjections/amigo/syntax"
	"github.com/despiteallobjections/amigo/types"
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
func Packages(initial []*packages.Package, mode types.BuilderMode) (*types.Program, []*types.SSAPackage) {
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
func AllPackages(initial []*packages.Package, mode types.BuilderMode) (*types.Program, []*types.SSAPackage) {
	return doPackages(initial, mode, true)
}

func doPackages(initial []*packages.Package, mode types.BuilderMode, deps bool) (*types.Program, []*types.SSAPackage) {
	prog := types.NewProgram(mode)

	isInitial := make(map[*packages.Package]bool, len(initial))
	for _, p := range initial {
		isInitial[p] = true
	}

	ssamap := make(map[*packages.Package]*types.SSAPackage)
	packages.Visit(initial, nil, func(p *packages.Package) {
		if p.PkgPath == "unsafe" {
			ssamap[p] = prog.CreatePackage(types.Unsafe, nil, nil, true)
			return
		}

		if len(p.CompiledGoFiles) == 0 {
			// TODO(mdempsky): Use srcimporter or import from p.ExportFile.
			panic(fmt.Errorf("missing source files for package %q", p.PkgPath))
		}

		files := make([]*syntax.File, len(p.CompiledGoFiles))
		for i, filename := range p.CompiledGoFiles {
			files[i], _ = syntax.ParseFile(filename, nil, nil, syntax.CheckBranches|syntax.AllowGenerics)
		}

		cfg := types.Config{
			Importer: &importer{
				imports: p.Imports,
				ssamap:  ssamap,
			},
		}

		if deps || isInitial[p] {
			cfg.Prog = prog
		}

		info := types.Info{
			Types:      make(map[syntax.Expr]types.TypeAndValue),
			Defs:       make(map[*syntax.Name]types.Object),
			Uses:       make(map[*syntax.Name]types.Object),
			Implicits:  make(map[syntax.Node]types.Object),
			Scopes:     make(map[syntax.Node]*types.Scope),
			Selections: make(map[*syntax.SelectorExpr]*types.Selection),
		}

		pkg, err := cfg.Check(p.PkgPath, files, &info)
		if err != nil {
			panic(fmt.Errorf("checking package %q failed: %w", p.PkgPath, err))
		}

		if cfg.Prog != nil {
			ssamap[p] = prog.Package(pkg)
		} else {
			ssamap[p] = prog.CreatePackage(pkg, nil, nil, true)
		}
	})

	var ssapkgs []*types.SSAPackage
	for _, p := range initial {
		ssapkgs = append(ssapkgs, ssamap[p]) // may be nil
	}
	return prog, ssapkgs
}

type importer struct {
	imports map[string]*packages.Package
	ssamap  map[*packages.Package]*types.SSAPackage
}

func (m *importer) Import(path, srcDir string) (*types.Package, error) {
	if pkg := m.ssamap[m.imports[path]]; pkg != nil {
		return pkg.Pkg, nil
	}
	return nil, fmt.Errorf("missing package for import path %q", path)
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
func CreateProgram(lprog *loader.Program, mode types.BuilderMode) *types.Program {
	prog := types.NewProgram(mode)

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
func BuildPackage(tc *types.Config, pkg *types.Package, files []*syntax.File, mode types.BuilderMode) (*types.Program, *types.SSAPackage, *types.Info, error) {
	if pkg.Path() == "" {
		panic("package has no import path")
	}

	prog := types.NewProgram(mode)
	tc.Prog = prog // TODO(mdempsky): Caller should handle this.

	info := &types.Info{
		Types:      make(map[syntax.Expr]types.TypeAndValue),
		Defs:       make(map[*syntax.Name]types.Object),
		Uses:       make(map[*syntax.Name]types.Object),
		Implicits:  make(map[syntax.Node]types.Object),
		Scopes:     make(map[syntax.Node]*types.Scope),
		Selections: make(map[*syntax.SelectorExpr]*types.Selection),
	}
	if err := types.NewChecker(tc, pkg, info).Files(files); err != nil {
		return nil, nil, nil, err
	}

	// Return the primary package, created/built by the type checker.
	return prog, prog.Package(pkg), info, nil
}
