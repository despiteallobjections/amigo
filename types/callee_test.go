// Copyright 2018 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package types_test

import (
	"go/build"
	"strings"
	"testing"

	"github.com/despiteallobjections/amigo/srcimporter"
	. "github.com/despiteallobjections/amigo/syntax"
	. "github.com/despiteallobjections/amigo/types"
)

func TestStaticCallee(t *testing.T) {
	const src = `package p

import "fmt"

type T int

func g(int)

var f = g

var x int

type s struct{ f func(int) }
func (s) g(int)

type I interface{ f(int) }

var a struct{b struct{c s}}

func calls() {
	g(x)           // a declared func
	s{}.g(x)       // a concrete method
	a.b.c.g(x)     // same
	fmt.Println(x) // declared func, qualified identifier
}

func noncalls() {
	_ = T(x)    // a type
	f(x)        // a var
	panic(x)    // a built-in
	s{}.f(x)    // a field
	I(nil).f(x) // interface method
}
`
	// parse
	f, err := ParseString("p.go", src)
	if err != nil {
		t.Fatal(err)
	}

	// type-check
	info := &Info{
		Uses:       make(map[*Name]Object),
		Selections: make(map[*SelectorExpr]*Selection),
	}
	cfg := &Config{Importer: srcimporter.New(&build.Default, map[string]*Package{})}
	if _, err := cfg.Check("p", []*File{f}, info); err != nil {
		t.Fatal(err)
	}

	for _, decl := range f.DeclList {
		if decl, ok := decl.(*FuncDecl); ok && strings.HasSuffix(decl.Name.Value, "calls") {
			wantCallee := decl.Name.Value == "calls" // false within func noncalls()
			Inspect(decl.Body, func(n Node) bool {
				if call, ok := n.(*CallExpr); ok {
					fn := StaticCallee(info, call)
					if fn == nil && wantCallee {
						t.Errorf("%s: StaticCallee returned nil", call.Pos())
					} else if fn != nil && !wantCallee {
						t.Errorf("%s: StaticCallee returned %s, want nil", call.Pos(), fn)
					}
				}
				return true
			})
		}
	}
}
