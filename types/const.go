// Copyright 2013 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package types

// This file defines the Const SSA value type.

import (
	"fmt"
	"go/constant"
	"strconv"

	. "github.com/despiteallobjections/amigo/syntax"
)

// NewSSAConst returns a new constant of the specified value and type.
// val must be valid according to the specification of Const.Value.
//
func NewSSAConst(val constant.Value, typ Type) *SSAConst {
	return &SSAConst{typ, val}
}

// intConst returns an 'int' constant that evaluates to i.
// (i is an int64 in case the host is narrower than the target.)
func intConst(i int64) *SSAConst {
	return NewSSAConst(constant.MakeInt64(i), tInt)
}

// nilConst returns a nil constant of the specified type, which may
// be any reference type, including interfaces.
//
func nilConst(typ Type) *SSAConst {
	return NewSSAConst(nil, typ)
}

// stringConst returns a 'string' constant that evaluates to s.
func stringConst(s string) *SSAConst {
	return NewSSAConst(constant.MakeString(s), tString)
}

// zeroConst returns a new "zero" constant of the specified type,
// which must not be an array or struct type: the zero values of
// aggregates are well-defined but cannot be represented by Const.
//
func zeroConst(t Type) *SSAConst {
	switch t := t.(type) {
	case *Basic:
		switch {
		case t.Info()&IsBoolean != 0:
			return NewSSAConst(constant.MakeBool(false), t)
		case t.Info()&IsNumeric != 0:
			return NewSSAConst(constant.MakeInt64(0), t)
		case t.Info()&IsString != 0:
			return NewSSAConst(constant.MakeString(""), t)
		case t.Kind() == UnsafePointer:
			fallthrough
		case t.Kind() == UntypedNil:
			return nilConst(t)
		default:
			panic(fmt.Sprint("zeroConst for unexpected type:", t))
		}
	case *Pointer, *Slice, *Interface, *Chan, *Map, *Signature:
		return nilConst(t)
	case *Named:
		return NewSSAConst(zeroConst(t.Underlying()).Value, t)
	case *Array, *Struct, *Tuple:
		panic(fmt.Sprint("zeroConst applied to aggregate:", t))
	}
	panic(fmt.Sprint("zeroConst: unexpected ", t))
}

func (c *SSAConst) RelString(from *Package) string {
	var s string
	if c.Value == nil {
		s = "nil"
	} else if c.Value.Kind() == constant.String {
		s = constant.StringVal(c.Value)
		const max = 20
		// TODO(adonovan): don't cut a rune in half.
		if len(s) > max {
			s = s[:max-3] + "..." // abbreviate
		}
		s = strconv.Quote(s)
	} else {
		s = c.Value.String()
	}
	return s + ":" + relType(c.Type(), from)
}

func (c *SSAConst) Name() string {
	return c.RelString(nil)
}

func (c *SSAConst) String() string {
	return c.Name()
}

func (c *SSAConst) Type() Type {
	return c.typ
}

func (c *SSAConst) Referrers() *[]Instruction {
	return nil
}

func (c *SSAConst) Parent() *Function { return nil }

func (c *SSAConst) Pos() Pos {
	return NoPos
}

// IsNil returns true if this constant represents a typed or untyped nil value.
func (c *SSAConst) IsNil() bool {
	return c.Value == nil
}

// TODO(adonovan): move everything below into golang.org/x/tools/go/ssa/interp.

// Int64 returns the numeric value of this constant truncated to fit
// a signed 64-bit integer.
//
func (c *SSAConst) Int64() int64 {
	switch x := constant.ToInt(c.Value); x.Kind() {
	case constant.Int:
		if i, ok := constant.Int64Val(x); ok {
			return i
		}
		return 0
	case constant.Float:
		f, _ := constant.Float64Val(x)
		return int64(f)
	}
	panic(fmt.Sprintf("unexpected constant value: %T", c.Value))
}

// Uint64 returns the numeric value of this constant truncated to fit
// an unsigned 64-bit integer.
//
func (c *SSAConst) Uint64() uint64 {
	switch x := constant.ToInt(c.Value); x.Kind() {
	case constant.Int:
		if u, ok := constant.Uint64Val(x); ok {
			return u
		}
		return 0
	case constant.Float:
		f, _ := constant.Float64Val(x)
		return uint64(f)
	}
	panic(fmt.Sprintf("unexpected constant value: %T", c.Value))
}

// Float64 returns the numeric value of this constant truncated to fit
// a float64.
//
func (c *SSAConst) Float64() float64 {
	f, _ := constant.Float64Val(c.Value)
	return f
}

// Complex128 returns the complex value of this constant truncated to
// fit a complex128.
//
func (c *SSAConst) Complex128() complex128 {
	re, _ := constant.Float64Val(constant.Real(c.Value))
	im, _ := constant.Float64Val(constant.Imag(c.Value))
	return complex(re, im)
}
