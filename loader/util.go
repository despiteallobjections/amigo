// Copyright 2013 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package loader

import (
	"go/build"
	"io"
	"os"
	"strconv"
	"sync"

	"github.com/mdempsky/amigo/syntax"
	"golang.org/x/tools/go/buildutil"
)

// We use a counting semaphore to limit
// the number of parallel I/O calls per process.
var ioLimit = make(chan bool, 10)

// parseFiles parses the Go source files within directory dir and
// returns the ASTs of the ones that could be at least partially parsed,
// along with a list of I/O and parse errors encountered.
//
// I/O is done via ctxt, which may specify a virtual file system.
// displayPath is used to transform the filenames attached to the ASTs.
//
func parseFiles(ctxt *build.Context, displayPath func(string) string, dir string, files []string) ([]*syntax.File, []error) {
	if displayPath == nil {
		displayPath = func(path string) string { return path }
	}
	var wg sync.WaitGroup
	n := len(files)
	parsed := make([]*syntax.File, n)
	errors := make([]error, n)
	for i, file := range files {
		if !buildutil.IsAbsPath(ctxt, file) {
			file = buildutil.JoinPath(ctxt, dir, file)
		}
		wg.Add(1)
		go func(i int, file string) {
			ioLimit <- true // wait
			defer func() {
				wg.Done()
				<-ioLimit // signal
			}()
			var rd io.ReadCloser
			var err error
			if ctxt.OpenFile != nil {
				rd, err = ctxt.OpenFile(file)
			} else {
				rd, err = os.Open(file)
			}
			if err != nil {
				errors[i] = err // open failed
				return
			}

			// ParseFile may return both an AST and an error.
			parsed[i], errors[i] = syntax.Parse(syntax.NewFileBase(displayPath(file)), rd, nil, nil, syntax.CheckBranches|syntax.AllowGenerics)
			rd.Close()
		}(i, file)
	}
	wg.Wait()

	// Eliminate nils, preserving order.
	var o int
	for _, f := range parsed {
		if f != nil {
			parsed[o] = f
			o++
		}
	}
	parsed = parsed[:o]

	o = 0
	for _, err := range errors {
		if err != nil {
			errors[o] = err
			o++
		}
	}
	errors = errors[:o]

	return parsed, errors
}

// scanImports returns the set of all import paths from all
// import specs in the specified files.
func scanImports(files []*syntax.File) map[string]bool {
	imports := make(map[string]bool)
	for _, f := range files {
		for _, decl := range f.DeclList {
			if decl, ok := decl.(*syntax.ImportDecl); ok {
				// NB: do not assume the program is well-formed!
				path, err := strconv.Unquote(decl.Path.Value)
				if err != nil {
					continue // quietly ignore the error
				}
				if path == "C" {
					continue // skip pseudopackage
				}
				imports[path] = true
			}
		}
	}
	return imports
}
