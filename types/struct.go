// Copyright 2021 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package types

import (
	"strconv"

	. "github.com/mdempsky/amigo/syntax"
)

// ----------------------------------------------------------------------------
// API

// A Struct represents a struct type.
type Struct struct {
	fields []*Var   // fields != nil indicates the struct is set up (possibly with len(fields) == 0)
	tags   []string // field tags; nil if there are no tags
}

// NewStruct returns a new struct with the given fields and corresponding field tags.
// If a field with index i has a tag, tags[i] must be that tag, but len(tags) may be
// only as long as required to hold the tag with the largest index i. Consequently,
// if no field has a tag, tags may be nil.
func NewStruct(fields []*Var, tags []string) *Struct {
	var fset objset
	for _, f := range fields {
		if f.name != "_" && fset.insert(f) != nil {
			panic("multiple fields with the same name")
		}
	}
	if len(tags) > len(fields) {
		panic("more tags than fields")
	}
	s := &Struct{fields: fields, tags: tags}
	s.markComplete()
	return s
}

// NumFields returns the number of fields in the struct (including blank and embedded fields).
func (s *Struct) NumFields() int { return len(s.fields) }

// Field returns the i'th field for 0 <= i < NumFields().
func (s *Struct) Field(i int) *Var { return s.fields[i] }

// Tag returns the i'th field tag for 0 <= i < NumFields().
func (s *Struct) Tag(i int) string {
	if i < len(s.tags) {
		return s.tags[i]
	}
	return ""
}

func (s *Struct) Underlying() Type { return s }
func (s *Struct) String() string   { return TypeString(s, nil) }

// ----------------------------------------------------------------------------
// Implementation

func (s *Struct) markComplete() {
	if s.fields == nil {
		s.fields = make([]*Var, 0)
	}
}

func (check *Checker) structType(styp *Struct, e *StructType) {
	if e.FieldList == nil {
		styp.markComplete()
		return
	}

	// struct fields and tags
	var fields []*Var
	var tags []string

	// for double-declaration checks
	var fset objset

	// current field typ and tag
	var typ Type
	var tag string
	add := func(ident *Name, embedded bool, pos Pos) {
		if tag != "" && tags == nil {
			tags = make([]string, len(fields))
		}
		if tags != nil {
			tags = append(tags, tag)
		}

		name := ident.Value
		fld := NewField(pos, check.pkg, name, typ, embedded)
		// spec: "Within a struct, non-blank field names must be unique."
		if name == "_" || check.declareInSet(&fset, pos, fld) {
			fields = append(fields, fld)
			check.recordDef(ident, fld)
		}
	}

	// addInvalid adds an embedded field of invalid type to the struct for
	// fields with errors; this keeps the number of struct fields in sync
	// with the source as long as the fields are _ or have different names
	// (issue #25627).
	addInvalid := func(ident *Name, pos Pos) {
		typ = Typ[Invalid]
		tag = ""
		add(ident, true, pos)
	}

	var prev Expr
	for i, f := range e.FieldList {
		// Fields declared syntactically with the same type (e.g.: a, b, c T)
		// share the same type expression. Only check type if it's a new type.
		if i == 0 || f.Type != prev {
			typ = check.varType(f.Type)
			prev = f.Type
		}
		tag = ""
		if i < len(e.TagList) {
			tag = check.tag(e.TagList[i])
		}
		if f.Name != nil {
			// named field
			add(f.Name, false, f.Name.Pos())
		} else {
			// embedded field
			// spec: "An embedded type must be specified as a type name T or as a
			// pointer to a non-interface type name *T, and T itself may not be a
			// pointer type."
			pos := StartPos(f.Type)
			name := embeddedFieldIdent(f.Type)
			if name == nil {
				check.errorf(pos, "invalid embedded field type %s", f.Type)
				name = &Name{Value: "_"} // TODO(gri) need to set position to pos
				addInvalid(name, pos)
				continue
			}
			add(name, true, pos)

			// Because we have a name, typ must be of the form T or *T, where T is the name
			// of a (named or alias) type, and t (= deref(typ)) must be the type of T.
			// We must delay this check to the end because we don't want to instantiate
			// (via under(t)) a possibly incomplete type.
			embeddedTyp := typ // for closure below
			embeddedPos := pos
			check.later(func() {
				t, isPtr := deref(embeddedTyp)
				switch u := under(t).(type) {
				case *Basic:
					if t == Typ[Invalid] {
						// error was reported before
						return
					}
					// unsafe.Pointer is treated like a regular pointer
					if u.kind == UnsafePointer {
						check.error(embeddedPos, "embedded field type cannot be unsafe.Pointer")
					}
				case *Pointer:
					check.error(embeddedPos, "embedded field type cannot be a pointer")
				case *Interface:
					if isTypeParam(t) {
						check.error(embeddedPos, "embedded field type cannot be a (pointer to a) type parameter")
						break
					}
					if isPtr {
						check.error(embeddedPos, "embedded field type cannot be a pointer to an interface")
					}
				}
			}).describef(embeddedPos, "check embedded type %s", embeddedTyp)
		}
	}

	styp.fields = fields
	styp.tags = tags
	styp.markComplete()
}

func embeddedFieldIdent(e Expr) *Name {
	switch e := e.(type) {
	case *Name:
		return e
	case *Operation:
		if base := ptrBase(e); base != nil {
			// *T is valid, but **T is not
			if op, _ := base.(*Operation); op == nil || ptrBase(op) == nil {
				return embeddedFieldIdent(e.X)
			}
		}
	case *SelectorExpr:
		return e.Sel
	case *IndexExpr:
		return embeddedFieldIdent(e.X)
	}
	return nil // invalid embedded field
}

func (check *Checker) declareInSet(oset *objset, pos Pos, obj Object) bool {
	if alt := oset.insert(obj); alt != nil {
		var err error_
		err.errorf(pos, "%s redeclared", obj.Name())
		err.recordAltDecl(alt)
		check.report(&err)
		return false
	}
	return true
}

func (check *Checker) tag(t *BasicLit) string {
	// If t.Bad, an error was reported during parsing.
	if t != nil && !t.Bad {
		if t.Kind == StringLit {
			if val, err := strconv.Unquote(t.Value); err == nil {
				return val
			}
		}
		check.errorf(t, invalidAST+"incorrect tag syntax: %q", t.Value)
	}
	return ""
}

func ptrBase(x *Operation) Expr {
	if x.Op == Mul && x.Y == nil {
		return x.X
	}
	return nil
}
