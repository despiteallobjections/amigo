// Copyright 2013 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// No testdata on Android.

//go:build !android
// +build !android

package ssautil_test

import (
	"io/ioutil"
	"testing"

	"github.com/despiteallobjections/amigo/loader"
	"github.com/despiteallobjections/amigo/ssa/ssautil"
	"github.com/despiteallobjections/amigo/types"
)

func TestSwitches(t *testing.T) {
	t.Skip("syntax.File doesn't support parsing comments")

	src, err := ioutil.ReadFile("testdata/switches.go")
	if err != nil {
		t.Error(err)
		return
	}

	conf := loader.Config{}
	f, err := conf.ParseFile("testdata/switches.go", string(src))
	if err != nil {
		t.Error(err)
		return
	}

	conf.CreateFromFiles("main", f)
	iprog, err := conf.Load()
	if err != nil {
		t.Error(err)
		return
	}

	prog := ssautil.CreateProgram(iprog, 0)
	mainPkg := prog.Package(iprog.Created[0].Pkg)
	mainPkg.Build(prog)

	for _, mem := range mainPkg.Members {
		if fn, ok := mem.(*types.Function); ok {
			if fn.Synthetic != "" {
				continue // e.g. init()
			}
			// Each (multi-line) "switch" comment within
			// this function must match the printed form
			// of a ConstSwitch.
			var wantSwitches []string
			/*
				for _, c := range f.Comments {
					if fn.Syntax().Pos() <= c.Pos() && c.Pos() < fn.Syntax().End() {
						text := strings.TrimSpace(c.Text())
						if strings.HasPrefix(text, "switch ") {
							wantSwitches = append(wantSwitches, text)
						}
					}
				}
			*/

			switches := ssautil.Switches(fn)
			if len(switches) != len(wantSwitches) {
				t.Errorf("in %s, found %d switches, want %d", fn, len(switches), len(wantSwitches))
			}
			for i, sw := range switches {
				got := sw.String()
				if i >= len(wantSwitches) {
					continue
				}
				want := wantSwitches[i]
				if got != want {
					t.Errorf("in %s, found switch %d: got <<%s>>, want <<%s>>", fn, i, got, want)
				}
			}
		}
	}
}
