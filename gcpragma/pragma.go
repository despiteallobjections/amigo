// Copyright 2016 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package gcpragma

import (
	"fmt"
	"path/filepath"
	"runtime"
	"strconv"
	"strings"
	"unicode"
	"unicode/utf8"

	"github.com/despiteallobjections/amigo/syntax"
)

func NewHandler(errh syntax.ErrorHandler) syntax.PragmaHandler {
	return &handler{
		errh: errh,
	}
}

type handler struct {
	pkgPrefix string // LocalPkg.Prefix

	errh       syntax.ErrorHandler
	linknames  []linkname
	pragcgobuf [][]string

	pragmas *pragmas
}

// TODO(mdempsky): Change these into noder fields.
const (
	base_Flag_CompilingRuntime     = false
	base_Flag_Std                  = false
	buildcfg_Experiment_FieldTrack = false
	buildcfg_GOOS                  = runtime.GOOS
)

// linkname records a //go:linkname directive.
type linkname struct {
	pos    syntax.Pos
	local  string
	remote string
}

type PragmaFlag uint16

const (
	// Func pragmas.
	Nointerface      PragmaFlag = 1 << iota
	Noescape                    // func parameters don't escape
	Norace                      // func must not have race detector annotations
	Nosplit                     // func should not execute on separate stack
	Noinline                    // func should not be inlined
	NoCheckPtr                  // func should not be instrumented by checkptr
	CgoUnsafeArgs               // treat a pointer to one arg as a pointer to them all
	UintptrKeepAlive            // pointers converted to uintptr must be kept alive (compiler internal only)
	UintptrEscapes              // pointers converted to uintptr escape

	// Runtime-only func pragmas.
	// See ../../../../runtime/HACKING.md for detailed descriptions.
	Systemstack        // func must run on system stack
	Nowritebarrier     // emit compiler error instead of write barrier
	Nowritebarrierrec  // error on write barrier in this or recursive callees
	Yeswritebarrierrec // cancels Nowritebarrierrec in this function and callees

	// Runtime and cgo type pragmas
	NotInHeap // values of this type must not be heap allocated

	// Go command pragmas
	GoBuildPragma

	RegisterParams // TODO(register args) remove after register abi is working
)

// *pragmas is the value stored in a syntax.pragmas during parsing.
type pragmas struct {
	Flag   PragmaFlag  // collected bits
	Pos    []pragmaPos // position of each individual flag
	Embeds []pragmaEmbed
}

type pragmaPos struct {
	Flag PragmaFlag
	Pos  syntax.Pos
}

type pragmaEmbed struct {
	Pos      syntax.Pos
	Patterns []string
}

func (h *handler) error(err error) {
	h.errh(err)
}

func (h *handler) take() *pragmas {
	res := h.pragmas
	h.pragmas = nil
	return res
}

func (h *handler) Add(pos syntax.Pos, text string) {
	if h.pragmas == nil {
		h.pragmas = new(pragmas)
	}
	pragma := h.pragmas

	if strings.HasPrefix(text, "line ") {
		// line directives are handled by syntax package
		panic("unreachable")
	}

	switch {
	case strings.HasPrefix(text, "go:linkname "):
		f := strings.Fields(text)
		if len(f) < 2 || len(f) > 3 {
			h.error(syntax.Error{Pos: pos, Msg: "usage: //go:linkname localname [linkname]"})
			break
		}
		// The second argument is optional. If omitted, we use
		// the default object symbol name for this and
		// linkname only serves to mark this symbol as
		// something that may be referenced via the object
		// symbol name from another package.
		var target string
		if len(f) == 3 {
			target = f[2]
		} else {
			// Use the default object symbol name if the
			// user didn't provide one.
			target = h.pkgPrefix + "." + f[1]
		}
		h.linknames = append(h.linknames, linkname{pos, f[1], target})

	case text == "go:embed", strings.HasPrefix(text, "go:embed "):
		args, err := parseGoEmbed(text[len("go:embed"):])
		if err != nil {
			h.error(syntax.Error{Pos: pos, Msg: err.Error()})
			break // TODO(mdempsky): Is this "break" missing from noder.go?
		}
		if len(args) == 0 {
			h.error(syntax.Error{Pos: pos, Msg: "usage: //go:embed pattern..."})
			break
		}
		pragma.Embeds = append(pragma.Embeds, pragmaEmbed{pos, args})

	case strings.HasPrefix(text, "go:cgo_import_dynamic "):
		// This is permitted for general use because Solaris
		// code relies on it in golang.org/x/sys/unix and others.
		fields := pragmaFields(text)
		if len(fields) >= 4 {
			lib := strings.Trim(fields[3], `"`)
			if lib != "" && !safeArg(lib) && !isCgoGeneratedFile(pos) {
				h.error(syntax.Error{Pos: pos, Msg: fmt.Sprintf("invalid library name %q in cgo_import_dynamic directive", lib)})
			}
			h.pragcgo(pos, text)
			pragma.Flag |= pragmaFlag("go:cgo_import_dynamic")
			break
		}
		fallthrough
	case strings.HasPrefix(text, "go:cgo_"):
		// For security, we disallow //go:cgo_* directives other
		// than cgo_import_dynamic outside cgo-generated files.
		// Exception: they are allowed in the standard library, for runtime and syscall.
		if !isCgoGeneratedFile(pos) && !base_Flag_Std {
			h.error(syntax.Error{Pos: pos, Msg: fmt.Sprintf("//%s only allowed in cgo-generated code", text)})
		}
		h.pragcgo(pos, text)
		fallthrough // because of //go:cgo_unsafe_args
	default:
		verb := text
		if i := strings.Index(text, " "); i >= 0 {
			verb = verb[:i]
		}
		flag := pragmaFlag(verb)
		const runtimePragmas = Systemstack | Nowritebarrier | Nowritebarrierrec | Yeswritebarrierrec
		if !base_Flag_CompilingRuntime && flag&runtimePragmas != 0 {
			h.error(syntax.Error{Pos: pos, Msg: fmt.Sprintf("//%s only allowed in runtime", verb)})
		}
		if flag == 0 && !allowedStdPragmas[verb] && base_Flag_Std {
			h.error(syntax.Error{Pos: pos, Msg: fmt.Sprintf("//%s is not allowed in the standard library", verb)})
		}
		pragma.Flag |= flag
		pragma.Pos = append(pragma.Pos, pragmaPos{flag, pos})
	}
}

func (h *handler) Take() syntax.Pragma {
	if res := h.take(); res != nil {
		return res
	}
	return nil // prevent returning syntax.Pragma((*pragmas)(nil))
}

func (h *handler) Reset() {
	pragma := h.take()
	if pragma == nil {
		return
	}

	for _, pos := range pragma.Pos {
		if pos.Flag&pragma.Flag != 0 {
			h.error(syntax.Error{Pos: pos.Pos, Msg: "misplaced compiler directive"})
		}
	}
	if len(pragma.Embeds) > 0 {
		for _, e := range pragma.Embeds {
			h.error(syntax.Error{Pos: e.Pos, Msg: "misplaced go:embed directive"})
		}
	}
}

// isCgoGeneratedFile reports whether pos is in a file
// generated by cgo, which is to say a file with name
// beginning with "_cgo_". Such files are allowed to
// contain cgo directives, and for security reasons
// (primarily misuse of linker flags), other files are not.
// See golang.org/issue/23672.
func isCgoGeneratedFile(pos syntax.Pos) bool {
	return strings.HasPrefix(filepath.Base(pos.Base().Filename()), "_cgo_")
}

// safeArg reports whether arg is a "safe" command-line argument,
// meaning that when it appears in a command-line, it probably
// doesn't have some special meaning other than its own name.
// This is copied from SafeArg in cmd/go/internal/load/pkg.go.
func safeArg(name string) bool {
	if name == "" {
		return false
	}
	c := name[0]
	return '0' <= c && c <= '9' || 'A' <= c && c <= 'Z' || 'a' <= c && c <= 'z' || c == '.' || c == '_' || c == '/' || c >= utf8.RuneSelf
}

// parseGoEmbed parses the text following "//go:embed" to extract the glob patterns.
// It accepts unquoted space-separated patterns as well as double-quoted and back-quoted Go strings.
// go/build/read.go also processes these strings and contains similar logic.
func parseGoEmbed(args string) ([]string, error) {
	var list []string
	for args = strings.TrimSpace(args); args != ""; args = strings.TrimSpace(args) {
		var path string
	Switch:
		switch args[0] {
		default:
			i := len(args)
			for j, c := range args {
				if unicode.IsSpace(c) {
					i = j
					break
				}
			}
			path = args[:i]
			args = args[i:]

		case '`':
			i := strings.Index(args[1:], "`")
			if i < 0 {
				return nil, fmt.Errorf("invalid quoted string in //go:embed: %s", args)
			}
			path = args[1 : 1+i]
			args = args[1+i+1:]

		case '"':
			i := 1
			for ; i < len(args); i++ {
				if args[i] == '\\' {
					i++
					continue
				}
				if args[i] == '"' {
					q, err := strconv.Unquote(args[:i+1])
					if err != nil {
						return nil, fmt.Errorf("invalid quoted string in //go:embed: %s", args[:i+1])
					}
					path = q
					args = args[i+1:]
					break Switch
				}
			}
			if i >= len(args) {
				return nil, fmt.Errorf("invalid quoted string in //go:embed: %s", args)
			}
		}

		if args != "" {
			r, _ := utf8.DecodeRuneInString(args)
			if !unicode.IsSpace(r) {
				return nil, fmt.Errorf("invalid quoted string in //go:embed: %s", args)
			}
		}
		list = append(list, path)
	}
	return list, nil
}

func isSpace(c rune) bool {
	return c == ' ' || c == '\t' || c == '\n' || c == '\r'
}

func isQuoted(s string) bool {
	return len(s) >= 2 && s[0] == '"' && s[len(s)-1] == '"'
}

const (
	funcPragmas = Nointerface |
		Noescape |
		Norace |
		Nosplit |
		Noinline |
		NoCheckPtr |
		RegisterParams | // TODO(register args) remove after register abi is working
		CgoUnsafeArgs |
		UintptrEscapes |
		Systemstack |
		Nowritebarrier |
		Nowritebarrierrec |
		Yeswritebarrierrec

	typePragmas = NotInHeap
)

func pragmaFlag(verb string) PragmaFlag {
	switch verb {
	case "go:build":
		return GoBuildPragma
	case "go:nointerface":
		if buildcfg_Experiment_FieldTrack {
			return Nointerface
		}
	case "go:noescape":
		return Noescape
	case "go:norace":
		return Norace
	case "go:nosplit":
		return Nosplit | NoCheckPtr // implies NoCheckPtr (see #34972)
	case "go:noinline":
		return Noinline
	case "go:nocheckptr":
		return NoCheckPtr
	case "go:systemstack":
		return Systemstack
	case "go:nowritebarrier":
		return Nowritebarrier
	case "go:nowritebarrierrec":
		return Nowritebarrierrec | Nowritebarrier // implies Nowritebarrier
	case "go:yeswritebarrierrec":
		return Yeswritebarrierrec
	case "go:cgo_unsafe_args":
		return CgoUnsafeArgs | NoCheckPtr // implies NoCheckPtr (see #34968)
	case "go:uintptrescapes":
		// For the next function declared in the file
		// any uintptr arguments may be pointer values
		// converted to uintptr. This directive
		// ensures that the referenced allocated
		// object, if any, is retained and not moved
		// until the call completes, even though from
		// the types alone it would appear that the
		// object is no longer needed during the
		// call. The conversion to uintptr must appear
		// in the argument list.
		// Used in syscall/dll_windows.go.
		return UintptrEscapes
	case "go:registerparams": // TODO(register args) remove after register abi is working
		return RegisterParams
	case "go:notinheap":
		return NotInHeap
	}
	return 0
}

// pragcgo is called concurrently if files are parsed concurrently.
func (p *handler) pragcgo(pos syntax.Pos, text string) {
	f := pragmaFields(text)

	verb := strings.TrimPrefix(f[0], "go:")
	f[0] = verb

	switch verb {
	case "cgo_export_static", "cgo_export_dynamic":
		switch {
		case len(f) == 2 && !isQuoted(f[1]):
		case len(f) == 3 && !isQuoted(f[1]) && !isQuoted(f[2]):
		default:
			p.error(syntax.Error{Pos: pos, Msg: fmt.Sprintf(`usage: //go:%s local [remote]`, verb)})
			return
		}
	case "cgo_import_dynamic":
		switch {
		case len(f) == 2 && !isQuoted(f[1]):
		case len(f) == 3 && !isQuoted(f[1]) && !isQuoted(f[2]):
		case len(f) == 4 && !isQuoted(f[1]) && !isQuoted(f[2]) && isQuoted(f[3]):
			f[3] = strings.Trim(f[3], `"`)
			if buildcfg_GOOS == "aix" && f[3] != "" {
				// On Aix, library pattern must be "lib.a/object.o"
				// or "lib.a/libname.so.X"
				n := strings.Split(f[3], "/")
				if len(n) != 2 || !strings.HasSuffix(n[0], ".a") || (!strings.HasSuffix(n[1], ".o") && !strings.Contains(n[1], ".so.")) {
					p.error(syntax.Error{Pos: pos, Msg: `usage: //go:cgo_import_dynamic local [remote ["lib.a/object.o"]]`})
					return
				}
			}
		default:
			p.error(syntax.Error{Pos: pos, Msg: `usage: //go:cgo_import_dynamic local [remote ["library"]]`})
			return
		}
	case "cgo_import_static":
		switch {
		case len(f) == 2 && !isQuoted(f[1]):
		default:
			p.error(syntax.Error{Pos: pos, Msg: `usage: //go:cgo_import_static local`})
			return
		}
	case "cgo_dynamic_linker":
		switch {
		case len(f) == 2 && isQuoted(f[1]):
			f[1] = strings.Trim(f[1], `"`)
		default:
			p.error(syntax.Error{Pos: pos, Msg: `usage: //go:cgo_dynamic_linker "path"`})
			return
		}
	case "cgo_ldflag":
		switch {
		case len(f) == 2 && isQuoted(f[1]):
			f[1] = strings.Trim(f[1], `"`)
		default:
			p.error(syntax.Error{Pos: pos, Msg: `usage: //go:cgo_ldflag "arg"`})
			return
		}
	default:
		return
	}
	p.pragcgobuf = append(p.pragcgobuf, f)
}

// pragmaFields is similar to strings.FieldsFunc(s, isSpace)
// but does not split when inside double quoted regions and always
// splits before the start and after the end of a double quoted region.
// pragmaFields does not recognize escaped quotes. If a quote in s is not
// closed the part after the opening quote will not be returned as a field.
func pragmaFields(s string) []string {
	var a []string
	inQuote := false
	fieldStart := -1 // Set to -1 when looking for start of field.
	for i, c := range s {
		switch {
		case c == '"':
			if inQuote {
				inQuote = false
				a = append(a, s[fieldStart:i+1])
				fieldStart = -1
			} else {
				inQuote = true
				if fieldStart >= 0 {
					a = append(a, s[fieldStart:i])
				}
				fieldStart = i
			}
		case !inQuote && isSpace(c):
			if fieldStart >= 0 {
				a = append(a, s[fieldStart:i])
				fieldStart = -1
			}
		default:
			if fieldStart == -1 {
				fieldStart = i
			}
		}
	}
	if !inQuote && fieldStart >= 0 { // Last field might end at the end of the string.
		a = append(a, s[fieldStart:])
	}
	return a
}

// pragmas that are allowed in the std lib, but don't have
// a syntax.Pragma value (see lex.go) associated with them.
var allowedStdPragmas = map[string]bool{
	"go:cgo_export_static":  true,
	"go:cgo_export_dynamic": true,
	"go:cgo_import_static":  true,
	"go:cgo_import_dynamic": true,
	"go:cgo_ldflag":         true,
	"go:cgo_dynamic_linker": true,
	"go:embed":              true,
	"go:generate":           true,
}
