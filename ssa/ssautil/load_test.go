// Copyright 2015 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssautil_test

import (
	"bytes"
	"os"
	"strings"
	"testing"

	"golang.org/x/tools/go/packages"

	"github.com/mdempsky/amigo/importer"
	"github.com/mdempsky/amigo/ssa/ssautil"
	"github.com/mdempsky/amigo/syntax"
	"github.com/mdempsky/amigo/testenv"
	"github.com/mdempsky/amigo/types"
)

const hello = `package main

import "fmt"

func main() {
	fmt.Println("Hello, world")
}
`

func TestBuildPackage(t *testing.T) {
	// There is a more substantial test of BuildPackage and the
	// SSA program it builds in ../ssa/builder_test.go.

	f, err := syntax.ParseString("hello.go", hello)
	if err != nil {
		t.Fatal(err)
	}

	pkg := types.NewPackage("hello", "")
	_, ssapkg, _, err := ssautil.BuildPackage(&types.Config{Importer: importer.Default()}, pkg, []*syntax.File{f}, 0)
	if err != nil {
		t.Fatal(err)
	}
	if pkg.Name() != "main" {
		t.Errorf("pkg.Name() = %s, want main", pkg.Name())
	}
	if ssapkg.Func("main") == nil {
		ssapkg.WriteTo(os.Stderr)
		t.Errorf("ssapkg has no main function")
	}
}

func TestPackages(t *testing.T) {
	testenv.NeedsGoPackages(t)

	cfg := &packages.Config{Mode: packages.LoadSyntax}
	initial, err := packages.Load(cfg, "bytes")
	if err != nil {
		t.Fatal(err)
	}
	if packages.PrintErrors(initial) > 0 {
		t.Fatal("there were errors")
	}

	prog, pkgs := ssautil.Packages(initial, 0)
	bytesNewBuffer := pkgs[0].Func("NewBuffer")
	bytesNewBuffer.Pkg.Build(prog)

	// We'll dump the SSA of bytes.NewBuffer because it is small and stable.
	out := new(bytes.Buffer)
	bytesNewBuffer.WriteTo(out)

	// For determinism, sanitize the location.
	location := bytesNewBuffer.Pos().String()
	got := strings.Replace(out.String(), location, "$GOROOT/src/bytes/buffer.go:1", -1)

	want := `
# Name: bytes.NewBuffer
# Package: bytes
# Location: $GOROOT/src/bytes/buffer.go:1
func NewBuffer(buf []byte) *Buffer:
0:                                                                entry P:0 S:0
	t0 = new Buffer (complit)                                       *Buffer
	t1 = &t0.buf [#0]                                               *[]byte
	*t1 = buf
	return t0

`[1:]
	if got != want {
		t.Errorf("bytes.NewBuffer SSA = <<%s>>, want <<%s>>", got, want)
	}
}

func TestBuildPackage_MissingImport(t *testing.T) {
	f, err := syntax.ParseString("bad.go", `package bad; import "missing"`)
	if err != nil {
		t.Fatal(err)
	}

	pkg := types.NewPackage("bad", "")
	_, ssapkg, _, err := ssautil.BuildPackage(new(types.Config), pkg, []*syntax.File{f}, 0)
	if err == nil || ssapkg != nil {
		t.Fatal("BuildPackage succeeded unexpectedly")
	}
}

func TestIssue28106(t *testing.T) {
	testenv.NeedsGoPackages(t)

	// In go1.10, go/packages loads all packages from source, not
	// export data, but does not type check function bodies of
	// imported packages. This test ensures that we do not attempt
	// to run the SSA builder on functions without type information.
	cfg := &packages.Config{Mode: packages.LoadSyntax}
	pkgs, err := packages.Load(cfg, "runtime")
	if err != nil {
		t.Fatal(err)
	}
	prog, _ := ssautil.Packages(pkgs, 0)
	prog.Build() // no crash
}
