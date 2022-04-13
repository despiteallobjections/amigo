// Copyright 2022 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package golden_test

import (
	"bytes"
	"runtime"
	"strings"
	"testing"

	"golang.org/x/tools/go/packages"
	oldssa "golang.org/x/tools/go/ssa"
	oldssautil "golang.org/x/tools/go/ssa/ssautil"

	newssautil "github.com/despiteallobjections/amigo/ssa/ssautil"
	"github.com/despiteallobjections/amigo/testenv"
	newssa "github.com/despiteallobjections/amigo/types"
	"github.com/pmezard/go-difflib/difflib"
)

func TestGolden(t *testing.T) {
	testenv.NeedsGoPackages(t)

	if strings.HasPrefix(runtime.Version(), "go1.17") {
		t.Skip("TODO(mdempsky): Get working with Go 1.17")
	}

	cfg := &packages.Config{Mode: packages.LoadAllSyntax}
	initial, err := packages.Load(cfg, "runtime", "fmt", "net/http")
	if err != nil {
		t.Fatal(err)
	}

	oldProg, _ := oldssautil.AllPackages(initial, oldssa.GlobalDebug)
	oldProg.Build()

	newProg, _ := newssautil.AllPackages(initial, newssa.GlobalDebug)

	for _, oldPkg := range oldProg.AllPackages() {
		path := oldPkg.Pkg.Path()
		if path == "unsafe" {
			continue
		}

		// TODO(mdempsky): Validate that all Syntax and Info match too.

		newPkg := newProg.ImportedPackage(path)
		if newPkg == nil {
			t.Errorf("missing package %q in newProg", path)
			continue
		}

		for name, oldMem := range oldPkg.Members {
			if oldFn, ok := oldMem.(*oldssa.Function); ok {
				newFn := newPkg.Members[name].(*newssa.Function)

				var oldBuf, newBuf bytes.Buffer
				oldssa.WriteFunction(&oldBuf, oldFn)
				newssa.WriteFunction(&newBuf, newFn)

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

					if text != "" {
						t.Error(text)
						continue
					}

					// TODO(mdempsky): Validate Instruction.Pos.
					// TODO(mdempsky): Anything else not included in Function.WriteTo output?
				}
			}
		}
	}
}
