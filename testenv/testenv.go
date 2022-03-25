// Copyright 2022 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package testenv

import (
	"os"
	"runtime"
	"testing"
)

// TODO(mdempsky): Remove these stubs.

func GOROOT(t testing.TB) string { return runtime.GOROOT() }
func Builder() string            { return os.Getenv("GO_BUILDER_NAME") }

func MustHaveGoBuild(t testing.TB) {}
func MustHaveCGO(t testing.TB)     {}

func HasSrc() bool { return true }
