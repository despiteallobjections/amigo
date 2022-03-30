// Copyright 2021 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

//go:build go1.17
// +build go1.17

package types_test

import (
	"testing"

	"github.com/mdempsky/amigo/importer"
	"github.com/mdempsky/amigo/ssa/ssautil"
	. "github.com/mdempsky/amigo/syntax"
	"github.com/mdempsky/amigo/types"
	. "github.com/mdempsky/amigo/types"
)

func TestBuildPackageGo117(t *testing.T) {
	tests := []struct {
		name     string
		src      string
		importer Importer
	}{
		{"slice to array pointer", "package p; var s []byte; var _ = (*[4]byte)(s)", nil},
		{"unsafe slice", `package p; import "unsafe"; var _ = unsafe.Add(nil, 0)`, importer.Default()},
		{"unsafe add", `package p; import "unsafe"; var _ = unsafe.Slice((*int)(nil), 0)`, importer.Default()},
	}

	for _, tc := range tests {
		tc := tc
		t.Run(tc.name, func(t *testing.T) {
			t.Parallel()
			f, err := ParseString("p.go", tc.src)
			if err != nil {
				t.Error(err)
			}
			files := []*File{f}

			pkg := NewPackage("p", "")
			conf := &Config{Importer: tc.importer}
			if _, _, err := ssautil.BuildPackage(conf, pkg, files, types.SanityCheckFunctions); err != nil {
				t.Errorf("unexpected error: %v", err)
			}
		})
	}
}

func TestBuildPackageFailuresGo117(t *testing.T) {
	tests := []struct {
		name     string
		src      string
		importer Importer
	}{
		{"slice to array pointer - source is not a slice", "package p; var s [4]byte; var _ = (*[4]byte)(s)", nil},
		{"slice to array pointer - dest is not a pointer", "package p; var s []byte; var _ = ([4]byte)(s)", nil},
		{"slice to array pointer - dest pointer elem is not an array", "package p; var s []byte; var _ = (*byte)(s)", nil},
	}

	for _, tc := range tests {
		tc := tc
		t.Run(tc.name, func(t *testing.T) {
			t.Parallel()
			f, err := ParseString("p.go", tc.src)
			if err != nil {
				t.Error(err)
			}
			files := []*File{f}

			pkg := NewPackage("p", "")
			conf := &Config{Importer: tc.importer}
			if _, _, err := ssautil.BuildPackage(conf, pkg, files, types.SanityCheckFunctions); err == nil {
				t.Error("want error, but got nil")
			}
		})
	}
}
