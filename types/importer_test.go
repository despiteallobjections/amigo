// Copyright 2022 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package types_test

import (
	"go/build"

	"github.com/mdempsky/amigo/srcimporter"
	"github.com/mdempsky/amigo/types"
)

// To avoid coupling to any particular compiler, we use srcimporter
// for tests. But to avoid too much slow down from having to
// repeatedly type check the entire package dependency subgraph, we
// reuse a single common importer across all tests.

var importer = srcimporter.New(&build.Default, map[string]*types.Package{})

func defaultImporter() types.Importer { return importer }
