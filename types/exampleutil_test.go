// Copyright 2014 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package types_test

import (
	"fmt"
	"sort"

	. "github.com/mdempsky/amigo/syntax"
	. "github.com/mdempsky/amigo/types"
)

func ExampleMap() {
	const source = `package P

var X []string
var Y []string

const p, q = 1.0, 2.0

func f(offset int32) (value byte, ok bool)
func g(rune) (uint8, bool)
`

	// Parse and type-check the package.
	f, err := ParseString("P.go", source)
	if err != nil {
		panic(err)
	}
	pkg, err := new(Config).Check("P", []*File{f}, nil)
	if err != nil {
		panic(err)
	}

	scope := pkg.Scope()

	// Group names of package-level objects by their type.
	var namesByType TypeMap // value is []string
	for _, name := range scope.Names() {
		T := scope.Lookup(name).Type()

		names, _ := namesByType.At(T).([]string)
		names = append(names, name)
		namesByType.Set(T, names)
	}

	// Format, sort, and print the map entries.
	var lines []string
	namesByType.Iterate(func(T Type, names interface{}) {
		lines = append(lines, fmt.Sprintf("%s   %s", names, T))
	})
	sort.Strings(lines)
	for _, line := range lines {
		fmt.Println(line)
	}

	// Output:
	// [X Y]   []string
	// [f g]   func(offset int32) (value byte, ok bool)
	// [p q]   untyped float
}
