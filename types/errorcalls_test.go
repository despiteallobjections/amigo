// Copyright 2021 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE ast.

package types_test

import (
	"testing"

	. "github.com/despiteallobjections/amigo/syntax"
)

// TestErrorCalls makes sure that check.errorf calls have at
// least 3 arguments (otherwise we should be using check.error).
func TestErrorCalls(t *testing.T) {
	files, err := pkgFiles(".")
	if err != nil {
		t.Fatal(err)
	}

	for _, file := range files {
		Crawl(file, func(n Node) bool {
			call, _ := n.(*CallExpr)
			if call == nil {
				return false
			}
			selx, _ := call.Fun.(*SelectorExpr)
			if selx == nil {
				return false
			}
			if !(isName(selx.X, "check") && isName(selx.Sel, "errorf")) {
				return false
			}
			// check.errorf calls should have more than 2 arguments:
			// position, format string, and arguments to format
			if n := len(call.ArgList); n <= 2 {
				t.Errorf("%s: got %d arguments, want > 2", call.Pos(), n)
				return true
			}
			return false
		})
	}
}

func isName(n Node, name string) bool {
	if n, ok := n.(*Name); ok {
		return n.Value == name
	}
	return false
}
