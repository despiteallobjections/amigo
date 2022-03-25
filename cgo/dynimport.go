// Copyright 2009 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package cgo

import (
	"debug/elf"
	"debug/macho"
	"debug/pe"
	"fmt"
	"os"
	"strings"
	"unicode"
)

// DynamicImports scans a gcc-produced executable
// and reports information about the imported symbols and the
// imported libraries. The 'go build' rules for cgo prepare an
// appropriate executable and then use its import information
// instead of needing to make the linkers duplicate all the
// specialized knowledge gcc has about where to look for imported
// symbols and which ones to use.
func DynamicImports(filename string) (interp string, imports [][3]string, err error) {
	if f, err := elf.Open(filename); err == nil {
		if sec := f.Section(".interp"); sec != nil {
			if data, err := sec.Data(); err == nil && len(data) > 1 {
				// skip trailing \0 in data
				interp = string(data[:len(data)-1])
			}
		}

		sym := elfImportedSymbols(f)
		for _, s := range sym {
			targ := s.Name
			if s.Version != "" {
				targ += "#" + s.Version
			}
			imports = append(imports, [3]string{s.Name, targ, s.Library})
		}
		lib, _ := f.ImportedLibraries()
		for _, l := range lib {
			imports = append(imports, [3]string{"_", "_", l})
		}
		return interp, imports, nil
	}

	if f, err := macho.Open(filename); err == nil {
		sym, _ := f.ImportedSymbols()
		for _, s := range sym {
			s = strings.TrimPrefix(s, "_")
			imports = append(imports, [3]string{s, s, ""})
		}
		lib, _ := f.ImportedLibraries()
		for _, l := range lib {
			imports = append(imports, [3]string{"_", "_", l})
		}
		return interp, imports, nil
	}

	if f, err := pe.Open(filename); err == nil {
		sym, _ := f.ImportedSymbols()
		for _, s := range sym {
			ss := strings.Split(s, ":")
			name := strings.Split(ss[0], "@")[0]
			imports = append(imports, [3]string{name, ss[0], strings.ToLower(ss[1])})
		}
		return interp, imports, nil
	}

	// TODO(mdempsky): Restore XCOFF support for AIX.
	/*
		if f, err := xcoff.Open(obj); err == nil {
			sym, err := f.ImportedSymbols()
			if err != nil {
				fatalf("cannot load imported symbols from XCOFF file %s: %v", obj, err)
			}
			for _, s := range sym {
				if s.Name == "runtime_rt0_go" || s.Name == "_rt0_ppc64_aix_lib" {
					// These symbols are imported by runtime/cgo but
					// must not be added to _cgo_import.go as there are
					// Go symbols.
					continue
				}
				checkImportSymName(s.Name)
				fmt.Fprintf(stdout, "//go:cgo_import_dynamic %s %s %q\n", s.Name, s.Name, s.Library)
			}
			lib, err := f.ImportedLibraries()
			if err != nil {
				fatalf("cannot load imported libraries from XCOFF file %s: %v", obj, err)
			}
			for _, l := range lib {
				fmt.Fprintf(stdout, "//go:cgo_import_dynamic _ _ %q\n", l)
			}
			return
		}
	*/

	return "", nil, fmt.Errorf("cannot parse %s as ELF, Mach-O, PE or XCOFF", filename)
}

// elfImportedSymbols is like elf.File.ImportedSymbols, but it
// includes weak symbols.
//
// A bug in some versions of LLD (at least LLD 8) cause it to emit
// several pthreads symbols as weak, but we need to import those. See
// issue #31912 or https://bugs.llvm.org/show_bug.cgi?id=42442.
//
// When doing external linking, we hand everything off to the external
// linker, which will create its own dynamic symbol tables. For
// internal linking, this may turn weak imports into strong imports,
// which could cause dynamic linking to fail if a symbol really isn't
// defined. However, the standard library depends on everything it
// imports, and this is the primary use of dynamic symbol tables with
// internal linking.
func elfImportedSymbols(f *elf.File) []elf.ImportedSymbol {
	syms, _ := f.DynamicSymbols()
	var imports []elf.ImportedSymbol
	for _, s := range syms {
		if (elf.ST_BIND(s.Info) == elf.STB_GLOBAL || elf.ST_BIND(s.Info) == elf.STB_WEAK) && s.Section == elf.SHN_UNDEF {
			imports = append(imports, elf.ImportedSymbol{
				Name:    s.Name,
				Library: s.Library,
				Version: s.Version,
			})
		}
	}
	return imports
}

// checkImportSymName checks a symbol name we are going to emit as part
// of a //go:cgo_import_dynamic pragma. These names come from object
// files, so they may be corrupt. We are going to emit them unquoted,
// so while they don't need to be valid symbol names (and in some cases,
// involving symbol versions, they won't be) they must contain only
// graphic characters and must not contain Go comments.
func checkImportSymName(s string) {
	for _, c := range s {
		if !unicode.IsGraphic(c) || unicode.IsSpace(c) {
			fatalf("dynamic symbol %q contains unsupported character", s)
		}
	}
	if strings.Contains(s, "//") || strings.Contains(s, "/*") {
		fatalf("dynamic symbol %q contains Go comment", s)
	}
}

// Die with an error message.
func fatalf(msg string, args ...interface{}) {
	// If we've already printed other errors, they might have
	// caused the fatal condition. Assume they're enough.
	if nerrors == 0 {
		fmt.Fprintf(os.Stderr, "cgo: "+msg+"\n", args...)
	}
	os.Exit(2)
}

var nerrors int
