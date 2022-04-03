// Copyright 2022 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package golden_test

import (
	"strings"
	"testing"

	"golang.org/x/tools/go/packages"
	oldssa "golang.org/x/tools/go/ssa"
	oldssautil "golang.org/x/tools/go/ssa/ssautil"

	newssautil "github.com/mdempsky/amigo/ssa/ssautil"
	"github.com/mdempsky/amigo/testenv"
	newssa "github.com/mdempsky/amigo/types"
	"github.com/pmezard/go-difflib/difflib"
)

func TestGolden(t *testing.T) {
	testenv.NeedsGoPackages(t)

	cfg := &packages.Config{Mode: packages.LoadAllSyntax}
	initial, err := packages.Load(cfg, "runtime", "fmt", "net/http")
	if err != nil {
		t.Fatal(err)
	}

	oldProg, _ := oldssautil.AllPackages(initial, 0)
	oldProg.Build()

	newProg, _ := newssautil.AllPackages(initial, 0)

	for _, oldPkg := range oldProg.AllPackages() {
		path := oldPkg.Pkg.Path()
		if path == "unsafe" {
			continue
		}

		newPkg := newProg.ImportedPackage(path)
		if newPkg == nil {
			t.Errorf("missing package %q in newProg", path)
			continue
		}

		for name, oldMem := range oldPkg.Members {
			if oldFn, ok := oldMem.(*oldssa.Function); ok {
				newFn := newPkg.Members[name].(*newssa.Function)

				var oldBuf, newBuf strings.Builder
				oldFn.WriteTo(&oldBuf)
				newFn.WriteTo(&newBuf)

				oldStr := oldBuf.String()
				newStr := newBuf.String()
				if oldStr != newStr {
					diff := difflib.UnifiedDiff{
						A:        difflib.SplitLines(oldStr),
						B:        difflib.SplitLines(newStr),
						FromFile: "Original",
						ToFile:   "Current",
						Context:  3,
					}
					text, err := difflib.GetUnifiedDiffString(diff)
					if err != nil {
						t.Fatal(err)
					}

					t.Error(text)
				}
			}
		}
	}
}
