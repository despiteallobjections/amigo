// Copyright 2013 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package types

import (
	. "github.com/despiteallobjections/amigo/syntax"
)

// labels checks correct label use in body.
func (check *Checker) labels(obj *Func, body *BlockStmt) {
	// set of all labels in this body
	all := NewScope(nil, body.Pos(), EndPos(body), "label")

	fwdJumps := check.blockBranches(obj, all, nil, nil, body.List)

	// If there are any forward jumps left, no label was found for
	// the corresponding goto statements. Either those labels were
	// never defined, or they are inside blocks and not reachable
	// for the respective gotos.
	for _, jmp := range fwdJumps {
		var msg string
		name := jmp.Label.Value
		if alt := all.Lookup(name); alt != nil {
			msg = "goto %s jumps into block"
			alt.(*Label).used = true // avoid another error
		} else {
			msg = "label %s not declared"
		}
		check.errorf(jmp.Label, msg, name)
	}

	// spec: "It is illegal to define a label that is never used."
	for name, obj := range all.elems {
		obj = resolve(name, obj)
		if lbl := obj.(*Label); !lbl.used {
			check.softErrorf(lbl.pos, "label %s declared but not used", lbl.name)
		}
	}
}

// A block tracks label declarations in a block and its enclosing blocks.
type block struct {
	parent *block                  // enclosing block
	lstmt  *LabeledStmt            // labeled statement to which this block belongs, or nil
	labels map[string]*LabeledStmt // allocated lazily
}

// insert records a new label declaration for the current block.
// The label must not have been declared before in any block.
func (b *block) insert(s *LabeledStmt) {
	name := s.Label.Value
	if debug {
		assert(b.gotoTarget(name) == nil)
	}
	labels := b.labels
	if labels == nil {
		labels = make(map[string]*LabeledStmt)
		b.labels = labels
	}
	labels[name] = s
}

// gotoTarget returns the labeled statement in the current
// or an enclosing block with the given label name, or nil.
func (b *block) gotoTarget(name string) *LabeledStmt {
	for s := b; s != nil; s = s.parent {
		if t := s.labels[name]; t != nil {
			return t
		}
	}
	return nil
}

// enclosingTarget returns the innermost enclosing labeled
// statement with the given label name, or nil.
func (b *block) enclosingTarget(name string) *LabeledStmt {
	for s := b; s != nil; s = s.parent {
		if t := s.lstmt; t != nil && t.Label.Value == name {
			return t
		}
	}
	return nil
}

// blockBranches processes a block's statement list and returns the set of outgoing forward jumps.
// all is the scope of all declared labels, parent the set of labels declared in the immediately
// enclosing block, and lstmt is the labeled statement this block is associated with (or nil).
func (check *Checker) blockBranches(obj *Func, all *Scope, parent *block, lstmt *LabeledStmt, list []Stmt) []*BranchStmt {
	b := &block{parent, lstmt, nil}

	var (
		varDeclPos         Pos
		fwdJumps, badJumps []*BranchStmt
	)

	// All forward jumps jumping over a variable declaration are possibly
	// invalid (they may still jump out of the block and be ok).
	// recordVarDecl records them for the given position.
	recordVarDecl := func(pos Pos) {
		varDeclPos = pos
		badJumps = append(badJumps[:0], fwdJumps...) // copy fwdJumps to badJumps
	}

	jumpsOverVarDecl := func(jmp *BranchStmt) bool {
		if varDeclPos.IsKnown() {
			for _, bad := range badJumps {
				if jmp == bad {
					return true
				}
			}
		}
		return false
	}

	var stmtBranches func(Stmt)
	stmtBranches = func(s Stmt) {
		switch s := s.(type) {
		case *DeclStmt:
			for _, d := range s.Decl.SpecList {
				if d, _ := d.(*VarSpec); d != nil {
					recordVarDecl(d.Pos())
				}
			}

		case *LabeledStmt:
			// declare non-blank label
			if name := s.Label.Value; name != "_" {
				lbl := NewLabel(s.Label.Pos(), check.pkg, name)
				lbl.index = len(obj.labels)
				obj.labels = append(obj.labels, lbl)
				if alt := all.Insert(lbl); alt != nil {
					var err error_
					err.soft = true
					err.errorf(lbl.pos, "label %s already declared", name)
					err.recordAltDecl(alt)
					check.report(&err)
					// ok to continue
				} else {
					b.insert(s)
					check.recordDef(s.Label, lbl)
				}
				// resolve matching forward jumps and remove them from fwdJumps
				i := 0
				for _, jmp := range fwdJumps {
					if jmp.Label.Value == name {
						// match
						lbl.used = true
						check.recordUse(jmp.Label, lbl)
						if jumpsOverVarDecl(jmp) {
							check.softErrorf(
								jmp.Label,
								"goto %s jumps over variable declaration at line %d",
								name,
								varDeclPos.Line(),
							)
							// ok to continue
						}
					} else {
						// no match - record new forward jump
						fwdJumps[i] = jmp
						i++
					}
				}
				fwdJumps = fwdJumps[:i]
				lstmt = s
			}
			stmtBranches(s.Stmt)

		case *BranchStmt:
			if s.Label == nil {
				return // checked in 1st pass (check.stmt)
			}

			// determine and validate target
			name := s.Label.Value
			switch s.Tok {
			case Break:
				// spec: "If there is a label, it must be that of an enclosing
				// "for", "switch", or "select" statement, and that is the one
				// whose execution terminates."
				valid := false
				if t := b.enclosingTarget(name); t != nil {
					switch t.Stmt.(type) {
					case *SwitchStmt, *SelectStmt, *ForStmt:
						valid = true
					}
				}
				if !valid {
					check.errorf(s.Label, "invalid break label %s", name)
					return
				}

			case Continue:
				// spec: "If there is a label, it must be that of an enclosing
				// "for" statement, and that is the one whose execution advances."
				valid := false
				if t := b.enclosingTarget(name); t != nil {
					switch t.Stmt.(type) {
					case *ForStmt:
						valid = true
					}
				}
				if !valid {
					check.errorf(s.Label, "invalid continue label %s", name)
					return
				}

			case Goto:
				if b.gotoTarget(name) == nil {
					// label may be declared later - add branch to forward jumps
					fwdJumps = append(fwdJumps, s)
					return
				}

			default:
				check.errorf(s, invalidAST+"branch statement: %s %s", s.Tok, name)
				return
			}

			// record label use
			obj := all.Lookup(name)
			obj.(*Label).used = true
			check.recordUse(s.Label, obj)

		case *AssignStmt:
			if s.Op == Def {
				recordVarDecl(s.Pos())
			}

		case *BlockStmt:
			// Unresolved forward jumps inside the nested block
			// become forward jumps in the current block.
			fwdJumps = append(fwdJumps, check.blockBranches(obj, all, b, lstmt, s.List)...)

		case *IfStmt:
			stmtBranches(s.Then)
			if s.Else != nil {
				stmtBranches(s.Else)
			}

		case *SwitchStmt:
			b := &block{b, lstmt, nil}
			for _, s := range s.Body {
				fwdJumps = append(fwdJumps, check.blockBranches(obj, all, b, nil, s.Body)...)
			}

		case *SelectStmt:
			b := &block{b, lstmt, nil}
			for _, s := range s.Body {
				fwdJumps = append(fwdJumps, check.blockBranches(obj, all, b, nil, s.Body)...)
			}

		case *ForStmt:
			stmtBranches(s.Body)
		}
	}

	for _, s := range list {
		stmtBranches(s)
	}

	return fwdJumps
}
