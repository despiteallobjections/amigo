// Copyright 2022 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package importer

import (
	"go/build"

	"github.com/despiteallobjections/amigo/srcimporter"
	"github.com/despiteallobjections/amigo/types"
)

var shared = srcimporter.New(&build.Default, map[string]*types.Package{})

func Default() types.Importer { return shared }
