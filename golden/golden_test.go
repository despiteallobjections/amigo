// Copyright 2022 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package golden_test

import (
	"testing"

	"golang.org/x/tools/go/packages"
	oldssa "golang.org/x/tools/go/ssa"
	oldssautil "golang.org/x/tools/go/ssa/ssautil"

	newssautil "github.com/mdempsky/amigo/ssa/ssautil"
	"github.com/mdempsky/amigo/testenv"
	newssa "github.com/mdempsky/amigo/types"
)

func TestGolden(t *testing.T) {
	testenv.NeedsGoPackages(t)

	cfg := &packages.Config{Mode: packages.LoadAllSyntax}
	initial, err := packages.Load(cfg, "fmt", "net/http")
	if err != nil {
		t.Fatal(err)
	}

	oldProg, oldPkgs := oldssautil.AllPackages(initial, 0)
	oldProg.Build()

	newProg, newPkgs := newssautil.AllPackages(initial, 0)
	newProg.Build()

	if len(oldPkgs) != len(newPkgs) {
		t.Fatalf("%v != %v", len(oldPkgs), len(newPkgs))
	}

	for i, oldPkg := range oldPkgs {
		newPkg := newPkgs[i]
		for name, oldMem := range oldPkg.Members {
			if oldFn, ok := oldMem.(*oldssa.Function); ok {
				newFn := newPkg.Members[name].(*newssa.Function)

				if len(oldFn.Blocks) != len(newFn.Blocks) {
					t.Fatalf("%v != %v", len(oldFn.Blocks), len(newFn.Blocks))
				}

				for j, oldBlock := range oldFn.Blocks {
					newBlock := newFn.Blocks[j]

					if oldBlock.Comment != newBlock.Comment {
						t.Errorf("block Comment: %q != %q at %v", oldBlock.Comment, newBlock.Comment, newBlock.Instrs[0].Pos())
					}

					if len(oldBlock.Instrs) != len(newBlock.Instrs) {
						t.Fatalf("%v != %v", len(oldBlock.Instrs), len(newBlock.Instrs))
					}

					for k, oldInstr := range oldBlock.Instrs {
						newInstr := newBlock.Instrs[k]

						oldString := oldInstr.String()
						newString := newInstr.String()

						if oldString != newString {
							t.Errorf("Instr.String: %q != %q", oldString, newString)
						}
					}
				}
			}
		}
	}
}
