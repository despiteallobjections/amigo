// Copyright 2013 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package types_test

import (
	"path"
	"path/filepath"
	"runtime"
	"testing"
	"time"

	. "github.com/mdempsky/amigo/syntax"
	. "github.com/mdempsky/amigo/types"
)

func TestSelf(t *testing.T) {
	files, err := pkgFiles(".")
	if err != nil {
		t.Fatal(err)
	}

	conf := Config{Importer: defaultImporter()}
	_, err = conf.Check("github.com/mdempsky/amigo/types", files, nil)
	if err != nil {
		t.Fatal(err)
	}
}

func BenchmarkCheck(b *testing.B) {
	for _, p := range []string{
		filepath.Join("src", "net", "http"),
		filepath.Join("src", "go", "parser"),
		filepath.Join("src", "go", "constant"),
		filepath.Join("src", "runtime"),
		filepath.Join("src", "go", "internal", "gcimporter"),
	} {
		b.Run(path.Base(p), func(b *testing.B) {
			path := filepath.Join(runtime.GOROOT(), p)
			for _, ignoreFuncBodies := range []bool{false, true} {
				name := "funcbodies"
				if ignoreFuncBodies {
					name = "nofuncbodies"
				}
				b.Run(name, func(b *testing.B) {
					b.Run("info", func(b *testing.B) {
						runbench(b, path, ignoreFuncBodies, true)
					})
					b.Run("noinfo", func(b *testing.B) {
						runbench(b, path, ignoreFuncBodies, false)
					})
				})
			}
		})
	}
}

func runbench(b *testing.B, path string, ignoreFuncBodies, writeInfo bool) {
	files, err := pkgFiles(path)
	if err != nil {
		b.Fatal(err)
	}

	// determine line count
	var lines uint
	for _, f := range files {
		lines += f.EOF.Line()
	}

	b.ResetTimer()
	start := time.Now()
	for i := 0; i < b.N; i++ {
		conf := Config{
			IgnoreFuncBodies: ignoreFuncBodies,
			Importer:         defaultImporter(),
		}
		var info *Info
		if writeInfo {
			info = &Info{
				Types:      make(map[Expr]TypeAndValue),
				Defs:       make(map[*Name]Object),
				Uses:       make(map[*Name]Object),
				Implicits:  make(map[Node]Object),
				Selections: make(map[*SelectorExpr]*Selection),
				Scopes:     make(map[Node]*Scope),
			}
		}
		if _, err := conf.Check(path, files, info); err != nil {
			b.Fatal(err)
		}
	}
	b.StopTimer()
	b.ReportMetric(float64(lines)*float64(b.N)/time.Since(start).Seconds(), "lines/s")
}

func pkgFiles(path string) ([]*File, error) {
	filenames, err := pkgFilenames(path) // from stdlib_test.go
	if err != nil {
		return nil, err
	}

	var files []*File
	for _, filename := range filenames {
		file, err := ParseFile(filename, nil, nil, 0)
		if err != nil {
			return nil, err
		}
		files = append(files, file)
	}

	return files, nil
}
