// Copyright 2016 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package typeutil_test

import (
	"fmt"
	"strings"
	"testing"

	"github.com/mdempsky/amigo/syntax"
	. "github.com/mdempsky/amigo/types"
	"github.com/mdempsky/amigo/typeutil"
)

func TestIntuitiveMethodSet(t *testing.T) {
	const source = `
package P
type A int
func (A) f()
func (*A) g()
`

	f, err := syntax.ParseString("hello.go", source)
	if err != nil {
		t.Fatal(err)
	}

	var conf Config
	pkg, err := conf.Check("P", []*syntax.File{f}, nil)
	if err != nil {
		t.Fatal(err)
	}
	qual := RelativeTo(pkg)

	for _, test := range []struct {
		expr string // type expression
		want string // intuitive method set
	}{
		{"A", "(A).f (*A).g"},
		{"*A", "(*A).f (*A).g"},
		{"error", "(error).Error"},
		{"*error", ""},
		{"struct{A}", "(struct{A}).f (*struct{A}).g"},
		{"*struct{A}", "(*struct{A}).f (*struct{A}).g"},
	} {
		tv, err := Eval(pkg, syntax.NoPos, test.expr)
		if err != nil {
			t.Errorf("Eval(%s) failed: %v", test.expr, err)
		}
		var names []string
		for _, m := range typeutil.IntuitiveMethodSet(tv.Type, nil) {
			name := fmt.Sprintf("(%s).%s", TypeString(m.Recv(), qual), m.Obj().Name())
			names = append(names, name)
		}
		got := strings.Join(names, " ")
		if got != test.want {
			t.Errorf("IntuitiveMethodSet(%s) = %q, want %q", test.expr, got, test.want)
		}
	}
}
