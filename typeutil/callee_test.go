// Copyright 2018 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package typeutil_test

import (
	"go/build"
	"strings"
	"testing"

	"github.com/mdempsky/amigo/srcimporter"
	"github.com/mdempsky/amigo/syntax"
	. "github.com/mdempsky/amigo/types"
	"github.com/mdempsky/amigo/typeutil"
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
	f, err := syntax.ParseString("p.go", src)
	if err != nil {
		t.Fatal(err)
	}

	// type-check
	info := &Info{
		Uses:       make(map[*syntax.Name]Object),
		Selections: make(map[*syntax.SelectorExpr]*Selection),
	}
	cfg := &Config{Importer: srcimporter.New(&build.Default, map[string]*Package{})}
	if _, err := cfg.Check("p", []*syntax.File{f}, info); err != nil {
		t.Fatal(err)
	}

	for _, decl := range f.DeclList {
		if decl, ok := decl.(*syntax.FuncDecl); ok && strings.HasSuffix(decl.Name.Value, "calls") {
			wantCallee := decl.Name.Value == "calls" // false within func noncalls()
			syntax.Inspect(decl.Body, func(n syntax.Node) bool {
				if call, ok := n.(*syntax.CallExpr); ok {
					fn := typeutil.StaticCallee(info, call)
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
