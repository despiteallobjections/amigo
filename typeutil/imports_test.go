// Copyright 2014 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package typeutil_test

import (
	"fmt"
	"strings"
	"testing"

	"github.com/mdempsky/amigo/syntax"
	"github.com/mdempsky/amigo/types"
	"github.com/mdempsky/amigo/typeutil"
)

type closure map[string]*types.Package

func (c closure) Import(path string) (*types.Package, error) { return c[path], nil }

func TestDependencies(t *testing.T) {
	packages := make(map[string]*types.Package)
	conf := types.Config{
		Importer: closure(packages),
	}

	// All edges go to the right.
	//  /--D--B--A
	// F    \_C_/
	//  \__E_/
	for i, content := range []string{
		`package a`,
		`package c; import (_ "a")`,
		`package b; import (_ "a")`,
		`package e; import (_ "c")`,
		`package d; import (_ "b"; _ "c")`,
		`package f; import (_ "d"; _ "e")`,
	} {
		f, err := syntax.Parse(syntax.NewFileBase(fmt.Sprintf("%d.go", i)), strings.NewReader(content), nil, nil, syntax.CheckBranches|syntax.AllowGenerics)
		if err != nil {
			t.Fatal(err)
		}
		pkg, err := conf.Check(f.PkgName.Value, []*syntax.File{f}, nil)
		if err != nil {
			t.Fatal(err)
		}
		packages[pkg.Path()] = pkg
	}

	for _, test := range []struct {
		roots, want string
	}{
		{"a", "a"},
		{"b", "ab"},
		{"c", "ac"},
		{"d", "abcd"},
		{"e", "ace"},
		{"f", "abcdef"},

		{"be", "abce"},
		{"eb", "aceb"},
		{"de", "abcde"},
		{"ed", "acebd"},
		{"ef", "acebdf"},
	} {
		var pkgs []*types.Package
		for _, r := range test.roots {
			pkgs = append(pkgs, packages[string(r)])
		}
		var got string
		for _, p := range typeutil.Dependencies(pkgs...) {
			got += p.Path()
		}
		if got != test.want {
			t.Errorf("Dependencies(%q) = %q, want %q", test.roots, got, test.want)
		}
	}
}
