// Copyright 2013 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package types

// This file defines a number of miscellaneous utility functions.

import (
	"fmt"
	"io"
	"os"

	. "github.com/despiteallobjections/amigo/syntax"
)

//// AST utilities

// isBlankIdent returns true iff e is an Ident with name "_".
// They have no associated types.Object, and thus no type.
//
func isBlankIdent(e Expr) bool {
	id, ok := e.(*Name)
	return ok && id.Value == "_"
}

//// Type utilities.  Some of these belong in github.com/despiteallobjections/amigo/types.

func isInterface(T Type) bool { return IsInterface(T) }

// deref returns a pointer's element type; otherwise it returns typ.
func ssaDeref(typ Type) Type {
	if p, ok := typ.Underlying().(*Pointer); ok {
		return p.Elem()
	}
	return typ
}

// recvType returns the receiver type of method obj.
func recvType(obj *Func) Type {
	return obj.Type().(*Signature).Recv().Type()
}

// logStack prints the formatted "start" message to stderr and
// returns a closure that prints the corresponding "end" message.
// Call using 'defer logStack(...)()' to show builder stack on panic.
// Don't forget trailing parens!
//
func logStack(format string, args ...interface{}) func() {
	msg := fmt.Sprintf(format, args...)
	io.WriteString(os.Stderr, msg)
	io.WriteString(os.Stderr, "\n")
	return func() {
		io.WriteString(os.Stderr, msg)
		io.WriteString(os.Stderr, " end\n")
	}
}

// newVar creates a 'var' for use in a types.Tuple.
func newVar(name string, typ Type) *Var {
	return NewParam(NoPos, nil, name, typ)
}

// anonVar creates an anonymous 'var' for use in a types.Tuple.
func anonVar(typ Type) *Var {
	return newVar("", typ)
}

var lenResults = NewTuple(anonVar(tInt))

// makeLen returns the len builtin specialized to type func(T)int.
func makeLen(T Type) *SSABuiltin {
	lenParams := NewTuple(anonVar(T))
	return &SSABuiltin{
		name: "len",
		sig:  NewSignatureType(nil, nil, nil, lenParams, lenResults, false),
	}
}
