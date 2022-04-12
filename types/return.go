// Copyright 2013 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// This file implements isTerminating.

package types

import (
	. "github.com/despiteallobjections/amigo/syntax"
)

// isTerminating reports if s is a terminating statement.
// If s is labeled, label is the label name; otherwise s
// is "".
func (check *Checker) isTerminating(s Stmt, label string) bool {
	switch s := s.(type) {
	default:
		unreachable()

	case *DeclStmt, *EmptyStmt, *SendStmt,
		*AssignStmt, *CallStmt:
		// no chance

	case *LabeledStmt:
		return check.isTerminating(s.Stmt, s.Label.Value)

	case *ExprStmt:
		// calling the predeclared (possibly parenthesized) panic() function is terminating
		if call, ok := Unparen(s.X).(*CallExpr); ok && check.isPanic[call] {
			return true
		}

	case *ReturnStmt:
		return true

	case *BranchStmt:
		if s.Tok == Goto || s.Tok == Fallthrough {
			return true
		}

	case *BlockStmt:
		return check.isTerminatingList(s.List, "")

	case *IfStmt:
		if s.Else != nil &&
			check.isTerminating(s.Then, "") &&
			check.isTerminating(s.Else, "") {
			return true
		}

	case *SwitchStmt:
		return check.isTerminatingSwitch(s.Body, label)

	case *SelectStmt:
		for _, cc := range s.Body {
			if !check.isTerminatingList(cc.Body, "") || hasBreakList(cc.Body, label, true) {
				return false
			}

		}
		return true

	case *ForStmt:
		if _, ok := s.Init.(*RangeClause); ok {
			// Range clauses guarantee that the loop terminates,
			// so the loop is not a terminating statement. See issue 49003.
			break
		}
		if s.Cond == nil && !hasBreak(s.Body, label, true) {
			return true
		}
	}

	return false
}

func (check *Checker) isTerminatingList(list []Stmt, label string) bool {
	// trailing empty statements are permitted - skip them
	for i := len(list) - 1; i >= 0; i-- {
		if _, ok := list[i].(*EmptyStmt); !ok {
			return check.isTerminating(list[i], label)
		}
	}
	return false // all statements are empty
}

func (check *Checker) isTerminatingSwitch(body []*CaseClause, label string) bool {
	hasDefault := false
	for _, cc := range body {
		if cc.Cases == nil {
			hasDefault = true
		}
		if !check.isTerminatingList(cc.Body, "") || hasBreakList(cc.Body, label, true) {
			return false
		}
	}
	return hasDefault
}

// TODO(gri) For nested breakable statements, the current implementation of hasBreak
//	     will traverse the same subtree repeatedly, once for each label. Replace
//           with a single-pass label/break matching phase.

// hasBreak reports if s is or contains a break statement
// referring to the label-ed statement or implicit-ly the
// closest outer breakable statement.
func hasBreak(s Stmt, label string, implicit bool) bool {
	switch s := s.(type) {
	default:
		unreachable()

	case *DeclStmt, *EmptyStmt, *ExprStmt,
		*SendStmt, *AssignStmt, *CallStmt,
		*ReturnStmt:
		// no chance

	case *LabeledStmt:
		return hasBreak(s.Stmt, label, implicit)

	case *BranchStmt:
		if s.Tok == Break {
			if s.Label == nil {
				return implicit
			}
			if s.Label.Value == label {
				return true
			}
		}

	case *BlockStmt:
		return hasBreakList(s.List, label, implicit)

	case *IfStmt:
		if hasBreak(s.Then, label, implicit) ||
			s.Else != nil && hasBreak(s.Else, label, implicit) {
			return true
		}

	case *SwitchStmt:
		if label != "" && hasBreakCaseList(s.Body, label, false) {
			return true
		}

	case *SelectStmt:
		if label != "" && hasBreakCommList(s.Body, label, false) {
			return true
		}

	case *ForStmt:
		if label != "" && hasBreak(s.Body, label, false) {
			return true
		}
	}

	return false
}

func hasBreakList(list []Stmt, label string, implicit bool) bool {
	for _, s := range list {
		if hasBreak(s, label, implicit) {
			return true
		}
	}
	return false
}

func hasBreakCaseList(list []*CaseClause, label string, implicit bool) bool {
	for _, s := range list {
		if hasBreakList(s.Body, label, implicit) {
			return true
		}
	}
	return false
}

func hasBreakCommList(list []*CommClause, label string, implicit bool) bool {
	for _, s := range list {
		if hasBreakList(s.Body, label, implicit) {
			return true
		}
	}
	return false
}
