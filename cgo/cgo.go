// Copyright 2013 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Package cgo handles cgo preprocessing of files containing `import "C"`.
//
// DESIGN
//
// The approach taken is to run the cgo processor on the package's
// CgoFiles and parse the output, faking the filenames of the
// resulting ASTs so that the synthetic file containing the C types is
// called "C" (e.g. "~/go/src/net/C") and the preprocessed files
// have their original names (e.g. "~/go/src/net/cgo_unix.go"),
// not the names of the actual temporary files.
//
// The advantage of this approach is its fidelity to 'go build'.  The
// downside is that the token.Position.Offset for each AST node is
// incorrect, being an offset within the temporary file.  Line numbers
// should still be correct because of the //line comments.
//
// The logic of this file is mostly plundered from the 'go build'
// tool, which also invokes the cgo preprocessor.
//
//
// REJECTED ALTERNATIVE
//
// An alternative approach that we explored is to extend go/types'
// Importer mechanism to provide the identity of the importing package
// so that each time `import "C"` appears it resolves to a different
// synthetic package containing just the objects needed in that case.
// The loader would invoke cgo but parse only the cgo_types.go file
// defining the package-level objects, discarding the other files
// resulting from preprocessing.
//
// The benefit of this approach would have been that source-level
// syntax information would correspond exactly to the original cgo
// file, with no preprocessing involved, making source tools like
// godoc, guru, and eg happy.  However, the approach was rejected
// due to the additional complexity it would impose on go/types.  (It
// made for a beautiful demo, though.)
//
// cgo files, despite their *.go extension, are not legal Go source
// files per the specification since they may refer to unexported
// members of package "C" such as C.int.  Also, a function such as
// C.getpwent has in effect two types, one matching its C type and one
// which additionally returns (errno C.int).  The cgo preprocessor
// uses name mangling to distinguish these two functions in the
// processed code, but go/types would need to duplicate this logic in
// its handling of function calls, analogous to the treatment of map
// lookups in which y=m[k] and y,ok=m[k] are both legal.

package cgo

import (
	"go/build"
	"os"
	"strings"

	exec "golang.org/x/sys/execabs"
)

// Command returns a prepared exec.Cmd to invoke the cgo preprocessor
// on bp.CgoFiles. The caller is responsible for running it.
func Command(bp *build.Package, pkgdir, tmpdir string) (*exec.Cmd, error) {
	args := []string{"cgotool", "-objdir", tmpdir}
	if bp.Goroot {
		switch bp.ImportPath {
		case "runtime/cgo":
			args = append(args, "-import_runtime_cgo=false", "-import_syscall=false")
		case "runtime/race":
			args = append(args, "-import_syscall=false")
		}
	}
	args = append(args, "--")
	args = append(args, strings.Fields(os.Getenv("CGO_CPPFLAGS"))...)
	args = append(args, bp.CgoCPPFLAGS...)

	cflags, err := PkgConfigFlags(bp)
	if err != nil {
		return nil, err
	}
	args = append(args, cflags...)

	// Allows including _cgo_export.h from .[ch] files in the package.
	args = append(args, "-I", tmpdir)

	args = append(args, strings.Fields(os.Getenv("CGO_CFLAGS"))...)
	args = append(args, bp.CgoCFLAGS...)

	args = append(args, bp.CgoFiles...)

	cmd := exec.Command(args[0], args[1:]...)
	cmd.Dir = pkgdir
	cmd.Env = append(os.Environ(), "PWD="+pkgdir)
	return cmd, nil
}
