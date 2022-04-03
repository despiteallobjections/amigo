// Copyright 2013 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package types

// This file implements the Function and BasicBlock types.

import (
	"bytes"
	"fmt"
	"io"
	"os"
	"strings"

	. "github.com/mdempsky/amigo/syntax"
)

// addEdge adds a control-flow graph edge from from to to.
func addEdge(from, to *BasicBlock) {
	from.Succs = append(from.Succs, to)
	to.Preds = append(to.Preds, from)
}

// Parent returns the function that contains block b.
func (b *BasicBlock) Parent() *Function { return b.parent }

// String returns a human-readable label of this block.
// It is not guaranteed unique within the function.
//
func (b *BasicBlock) String() string {
	return fmt.Sprintf("%d", b.Index)
}

// emit appends an instruction to the current basic block.
// If the instruction defines a Value, it is returned.
//
func (b *BasicBlock) emit(i Instruction) Value {
	i.setBlock(b)
	b.Instrs = append(b.Instrs, i)
	v, _ := i.(Value)
	return v
}

// predIndex returns the i such that b.Preds[i] == c or panics if
// there is none.
func (b *BasicBlock) predIndex(c *BasicBlock) int {
	for i, pred := range b.Preds {
		if pred == c {
			return i
		}
	}
	panic(fmt.Sprintf("no edge %s -> %s", c, b))
}

// hasPhi returns true if b.Instrs contains φ-nodes.
func (b *BasicBlock) hasPhi() bool {
	_, ok := b.Instrs[0].(*Phi)
	return ok
}

// phis returns the prefix of b.Instrs containing all the block's φ-nodes.
func (b *BasicBlock) phis() []Instruction {
	for i, instr := range b.Instrs {
		if _, ok := instr.(*Phi); !ok {
			return b.Instrs[:i]
		}
	}
	return nil // unreachable in well-formed blocks
}

// replacePred replaces all occurrences of p in b's predecessor list with q.
// Ordinarily there should be at most one.
//
func (b *BasicBlock) replacePred(p, q *BasicBlock) {
	for i, pred := range b.Preds {
		if pred == p {
			b.Preds[i] = q
		}
	}
}

// replaceSucc replaces all occurrences of p in b's successor list with q.
// Ordinarily there should be at most one.
//
func (b *BasicBlock) replaceSucc(p, q *BasicBlock) {
	for i, succ := range b.Succs {
		if succ == p {
			b.Succs[i] = q
		}
	}
}

// removePred removes all occurrences of p in b's
// predecessor list and φ-nodes.
// Ordinarily there should be at most one.
//
func (b *BasicBlock) removePred(p *BasicBlock) {
	phis := b.phis()

	// We must preserve edge order for φ-nodes.
	j := 0
	for i, pred := range b.Preds {
		if pred != p {
			b.Preds[j] = b.Preds[i]
			// Strike out φ-edge too.
			for _, instr := range phis {
				phi := instr.(*Phi)
				phi.Edges[j] = phi.Edges[i]
			}
			j++
		}
	}
	// Nil out b.Preds[j:] and φ-edges[j:] to aid GC.
	for i := j; i < len(b.Preds); i++ {
		b.Preds[i] = nil
		for _, instr := range phis {
			instr.(*Phi).Edges[i] = nil
		}
	}
	b.Preds = b.Preds[:j]
	for _, instr := range phis {
		phi := instr.(*Phi)
		phi.Edges = phi.Edges[:j]
	}
}

// Destinations associated with unlabelled for/switch/select stmts.
// We push/pop one of these as we enter/leave each construct and for
// each BranchStmt we scan for the innermost target of the right type.
//
type targets struct {
	tail         *targets // rest of stack
	_break       *BasicBlock
	_continue    *BasicBlock
	_fallthrough *BasicBlock
}

// Destinations associated with a labelled block.
// We populate these as labels are encountered in forward gotos or
// labelled statements.
//
type lblock struct {
	_goto     *BasicBlock
	_break    *BasicBlock
	_continue *BasicBlock
}

// labelledBlock returns the branch target associated with the
// specified label, creating it if needed.
//
func (b *builder) labelledBlock(label *Name) *lblock {
	// TODO(mdempsky): This used to be keyed by label.Object, but now
	// I'm using label.Value. I think that's safe, but double check that
	// it doesn't cause problems with closures and identically named
	// labels.

	lb := b.lblocks[label.Value]
	if lb == nil {
		lb = &lblock{_goto: b.newBasicBlock(label.Value)}
		if b.lblocks == nil {
			b.lblocks = make(map[string]*lblock)
		}
		b.lblocks[label.Value] = lb
	}
	return lb
}

// addParamObj adds a (non-escaping) parameter to f.Params for the
// specified Var.
//
func (b *builder) addParamObj(obj *Var) { b.addParam(obj, false) }

// addSpilledParam declares a parameter that is pre-spilled to the
// stack; the function body will load/store the spilled location.
// Subsequent lifting will eliminate spills where possible.
//
func (b *builder) addSpilledParam(obj *Var) { b.addParam(obj, true) }

// addParamObj adds a (non-escaping) parameter to f.Params for the
// specified Var.
//
// If spill is true, then the parameter is pre-spilled to the stack;
// the function body will load/store the spilled location. Subsequent
// lifting will eliminate spills where possible.
//
func (b *builder) addParam(obj *Var, spill bool) {
	f := b.Fn
	name := obj.Name()
	if name == "" {
		name = fmt.Sprintf("arg%d", len(f.Params))
	}
	param := &Parameter{
		name:   name,
		object: obj,
		parent: f,
	}
	f.Params = append(f.Params, param)

	if spill {
		alloc := &Alloc{Comment: obj.Name()}
		alloc.setType(NewPointer(obj.Type()))
		alloc.setPos(obj.Pos())
		b.objects[obj] = alloc
		f.Locals = append(f.Locals, alloc)
		b.emit(alloc)
		b.emit(&Store{Addr: alloc, Val: param})
	}
}

// startBody initializes the function prior to generating SSA code for its body.
// Precondition: f.Type() already set.
//
func (b *builder) startBody() {
	b.currentBlock = b.newBasicBlock("entry")
	b.objects = make(map[*Var]Value) // needed for some synthetics, e.g. init
}

// createSyntacticParams populates f.Params and generates code (spills
// and named result locals) for all the parameters declared in the
// syntax.  In addition it populates the f.objects mapping.
//
// Preconditions:
// f.startBody() was called.
// Postcondition:
// len(f.Params) == len(f.Signature.Params) + (f.Signature.Recv() ? 1 : 0)
//
func (b *builder) createSyntacticParams() {
	f := b.Fn
	if recv := f.Signature.Recv(); recv != nil {
		b.addParam(recv, recv.Name() != "")
	}

	// Parameters.
	params := f.Signature.Params()
	for i := 0; i < params.Len(); i++ {
		param := params.At(i)
		b.addParam(param, param.Name() != "")
	}

	// Named results.
	results := f.Signature.Results()
	for i := 0; i < results.Len(); i++ {
		result := results.At(i)
		if result.Name() != "" {
			// Implicit "var" decl of locals for named results.
			b.namedResults = append(b.namedResults, b.addNamedLocal(result))
		}
	}
}

type setNumable interface {
	setNum(int)
}

// numberRegisters assigns numbers to all SSA registers
// (value-defining Instructions) in f, to aid debugging.
// (Non-Instruction Values are named at construction.)
//
func numberRegisters(b *builder) {
	f := b.Fn
	v := 0
	for _, b := range f.Blocks {
		for _, instr := range b.Instrs {
			switch instr.(type) {
			case Value:
				instr.(setNumable).setNum(v)
				v++
			}
		}
	}
}

// buildReferrers populates the def/use information in all non-nil
// Value.Referrers slice.
// Precondition: all such slices are initially empty.
func buildReferrers(b *builder) {
	f := b.Fn
	var rands []*Value
	for _, b := range f.Blocks {
		for _, instr := range b.Instrs {
			rands = instr.Operands(rands[:0]) // recycle storage
			for _, rand := range rands {
				if r := *rand; r != nil {
					if ref := r.Referrers(); ref != nil {
						*ref = append(*ref, instr)
					}
				}
			}
		}
	}
}

// finishBody() finalizes the function after SSA code generation of its body.
func (b *builder) finishBody() {
	f := b.Fn
	b.objects = nil
	b.currentBlock = nil
	b.lblocks = nil
	f.syntax = nil

	// Remove from f.Locals any Allocs that escape to the heap.
	j := 0
	for _, l := range f.Locals {
		if !l.Heap {
			f.Locals[j] = l
			j++
		}
	}
	// Nil out f.Locals[j:] to aid GC.
	for i := j; i < len(f.Locals); i++ {
		f.Locals[i] = nil
	}
	f.Locals = f.Locals[:j]

	optimizeBlocks(b)

	buildReferrers(b)

	buildDomTree(b)

	if b.Prog.mode&NaiveForm == 0 {
		// For debugging pre-state of lifting pass:
		// numberRegisters(f)
		// f.WriteTo(os.Stderr)
		lift(b)
	}

	b.namedResults = nil // (used by lifting)

	numberRegisters(b)

	if b.Prog.mode&PrintFunctions != 0 {
		printMu.Lock()
		f.WriteTo(os.Stdout)
		printMu.Unlock()
	}

	if b.Prog.mode&SanityCheckFunctions != 0 {
		mustSanityCheck(f, nil)
	}
}

// removeNilBlocks eliminates nils from f.Blocks and updates each
// BasicBlock.Index.  Use this after any pass that may delete blocks.
//
func (f *Function) removeNilBlocks() {
	j := 0
	for _, b := range f.Blocks {
		if b != nil {
			b.Index = j
			f.Blocks[j] = b
			j++
		}
	}
	// Nil out f.Blocks[j:] to aid GC.
	for i := j; i < len(f.Blocks); i++ {
		f.Blocks[i] = nil
	}
	f.Blocks = f.Blocks[:j]
}

// SetDebugMode sets the debug mode for package pkg.  If true, all its
// functions will include full debug info.  This greatly increases the
// size of the instruction stream, and causes Functions to depend upon
// the ASTs, potentially keeping them live in memory for longer.
//
func (pkg *SSAPackage) SetDebugMode(debug bool) {
	// TODO(adonovan): do we want syntax.File granularity?
	pkg.debug = debug
}

// debugInfo reports whether debug info is wanted for this function.
func (f *Function) debugInfo() bool {
	return f.Pkg != nil && f.Pkg.debug
}

// addNamedLocal creates a local variable, adds it to function f and
// returns it.  Its name and type are taken from obj.  Subsequent
// calls to f.lookup(obj) will return the same local.
//
func (b *builder) addNamedLocal(obj *Var) *Alloc {
	l := b.addLocal(obj.Type(), obj.Pos())
	l.Comment = obj.Name()
	b.objects[obj] = l
	return l
}

func (b *builder) addLocalForIdent(id *Name) *Alloc {
	return b.addNamedLocal(b.Fn.Pkg.info.Defs[id].(*Var))
}

// addLocal creates an anonymous local variable of type typ, adds it
// to function f and returns it.  pos is the optional source location.
//
func (b *builder) addLocal(typ Type, pos Pos) *Alloc {
	fn := b.Fn
	v := &Alloc{}
	v.setType(NewPointer(typ))
	v.setPos(pos)
	fn.Locals = append(fn.Locals, v)
	b.emit(v)
	return v
}

// lookup returns the address of the named variable identified by obj
// that is local to function f or one of its enclosing functions.
// If escaping, the reference comes from a potentially escaping pointer
// expression and the referent must be heap-allocated.
//
func (b *builder) lookup(f *Function, obj *Var, escaping bool) Value {
	if v, ok := b.objects[obj]; ok {
		if alloc, ok := v.(*Alloc); ok && escaping {
			alloc.Heap = true
		}
		return v // function-local var (address)
	}

	// Definition must be in an enclosing function;
	// plumb it through intervening closures.
	if f.parent == nil {
		panic("no ssa.Value for " + obj.String())
	}
	v := &FreeVar{
		object: obj,
		typ:    NewPointer(obj.Type()),
		parent: f,
	}
	b.objects[obj] = v
	f.FreeVars = append(f.FreeVars, v)
	return v
}

// emit emits the specified instruction to function f.
func (b *builder) emit(instr Instruction) Value {
	return b.currentBlock.emit(instr)
}

// RelString returns the full name of this function, qualified by
// package name, receiver type, etc.
//
// The specific formatting rules are not guaranteed and may change.
//
// Examples:
//      "math.IsNaN"                  // a package-level function
//      "(*bytes.Buffer).Bytes"       // a declared method or a wrapper
//      "(*bytes.Buffer).Bytes$thunk" // thunk (func wrapping method; receiver is param 0)
//      "(*bytes.Buffer).Bytes$bound" // bound (func wrapping method; receiver supplied by closure)
//      "main.main$1"                 // an anonymous function in main
//      "main.init#1"                 // a declared init function
//      "main.init"                   // the synthesized package initializer
//
// When these functions are referred to from within the same package
// (i.e. from == f.Pkg.Object), they are rendered without the package path.
// For example: "IsNaN", "(*Buffer).Bytes", etc.
//
// All non-synthetic functions have distinct package-qualified names.
// (But two methods may have the same name "(T).f" if one is a synthetic
// wrapper promoting a non-exported method "f" from another package; in
// that case, the strings are equal but the identifiers "f" are distinct.)
//
func (f *Function) RelString(from *Package) string {
	// Anonymous?
	if f.parent != nil {
		// An anonymous function's Name() looks like "parentName$1",
		// but its String() should include the type/package/etc.
		parent := f.parent.RelString(from)
		for i, anon := range f.parent.AnonFuncs {
			if anon == f {
				return fmt.Sprintf("%s$%d", parent, 1+i)
			}
		}

		return f.name // should never happen
	}

	// Method (declared or wrapper)?
	if recv := f.Signature.Recv(); recv != nil {
		return f.relMethod(from, recv.Type())
	}

	// Thunk?
	if f.method != nil {
		return f.relMethod(from, f.method.Recv())
	}

	// Bound?
	if len(f.FreeVars) == 1 && strings.HasSuffix(f.name, "$bound") {
		return f.relMethod(from, f.FreeVars[0].Type())
	}

	// Package-level function?
	// Prefix with package name for cross-package references only.
	if p := f.pkg(); p != nil && p != from {
		return fmt.Sprintf("%s.%s", p.Path(), f.name)
	}

	// Unknown.
	return f.name
}

func (f *Function) relMethod(from *Package, recv Type) string {
	return fmt.Sprintf("(%s).%s", relType(recv, from), f.name)
}

// writeSignature writes to buf the signature sig in declaration syntax.
func writeSignature(buf *bytes.Buffer, from *Package, name string, sig *Signature, params []*Parameter) {
	buf.WriteString("func ")
	if recv := sig.Recv(); recv != nil {
		buf.WriteString("(")
		if n := params[0].Name(); n != "" {
			buf.WriteString(n)
			buf.WriteString(" ")
		}
		WriteType(buf, params[0].Type(), RelativeTo(from))
		buf.WriteString(") ")
	}
	buf.WriteString(name)
	WriteSignature(buf, sig, RelativeTo(from))
}

func (f *Function) pkg() *Package {
	if f.Pkg != nil {
		return f.Pkg.Pkg
	}
	return nil
}

var _ io.WriterTo = (*Function)(nil) // *Function implements io.Writer

func (f *Function) WriteTo(w io.Writer) (int64, error) {
	var buf bytes.Buffer
	WriteFunction(&buf, f)
	n, err := w.Write(buf.Bytes())
	return int64(n), err
}

// WriteFunction writes to buf a human-readable "disassembly" of f.
func WriteFunction(buf *bytes.Buffer, f *Function) {
	fmt.Fprintf(buf, "# Name: %s\n", f.String())
	if f.Pkg != nil {
		fmt.Fprintf(buf, "# Package: %s\n", f.Pkg.Pkg.Path())
	}
	if syn := f.Synthetic; syn != "" {
		fmt.Fprintln(buf, "# Synthetic:", syn)
	}
	if pos := f.Pos(); pos.IsValid() {
		fmt.Fprintf(buf, "# Location: %s\n", pos)
	}

	if f.parent != nil {
		fmt.Fprintf(buf, "# Parent: %s\n", f.parent.Name())
	}

	if f.Recover != nil {
		fmt.Fprintf(buf, "# Recover: %s\n", f.Recover)
	}

	from := f.pkg()

	if f.FreeVars != nil {
		buf.WriteString("# Free variables:\n")
		for i, fv := range f.FreeVars {
			fmt.Fprintf(buf, "# % 3d:\t%s %s\n", i, fv.Name(), relType(fv.Type(), from))
		}
	}

	if len(f.Locals) > 0 {
		buf.WriteString("# Locals:\n")
		for i, l := range f.Locals {
			fmt.Fprintf(buf, "# % 3d:\t%s %s\n", i, l.Name(), relType(ssaDeref(l.Type()), from))
		}
	}
	writeSignature(buf, from, f.Name(), f.Signature, f.Params)
	buf.WriteString(":\n")

	if f.Blocks == nil {
		buf.WriteString("\t(external)\n")
	}

	// NB. column calculations are confused by non-ASCII
	// characters and assume 8-space tabs.
	const punchcard = 80 // for old time's sake.
	const tabwidth = 8
	for _, b := range f.Blocks {
		if b == nil {
			// Corrupt CFG.
			fmt.Fprintf(buf, ".nil:\n")
			continue
		}
		n, _ := fmt.Fprintf(buf, "%d:", b.Index)
		bmsg := fmt.Sprintf("%s P:%d S:%d", b.Comment, len(b.Preds), len(b.Succs))
		fmt.Fprintf(buf, "%*s%s\n", punchcard-1-n-len(bmsg), "", bmsg)

		if false { // CFG debugging
			fmt.Fprintf(buf, "\t# CFG: %s --> %s --> %s\n", b.Preds, b, b.Succs)
		}
		for _, instr := range b.Instrs {
			buf.WriteString("\t")
			switch v := instr.(type) {
			case Value:
				l := punchcard - tabwidth
				// Left-align the instruction.
				if name := v.Name(); name != "" {
					n, _ := fmt.Fprintf(buf, "%s = ", name)
					l -= n
				}
				n, _ := buf.WriteString(instr.String())
				l -= n
				// Right-align the type if there's space.
				if t := v.Type(); t != nil {
					buf.WriteByte(' ')
					ts := relType(t, from)
					l -= len(ts) + len("  ") // (spaces before and after type)
					if l > 0 {
						fmt.Fprintf(buf, "%*s", l, "")
					}
					buf.WriteString(ts)
				}
			case nil:
				// Be robust against bad transforms.
				buf.WriteString("<deleted>")
			default:
				buf.WriteString(instr.String())
			}
			buf.WriteString("\n")
		}
	}
	fmt.Fprintf(buf, "\n")
}

// newBasicBlock adds to f a new basic block and returns it.  It does
// not automatically become the current block for subsequent calls to emit.
// comment is an optional string for more readable debugging output.
//
func (b *builder) newBasicBlock(comment string) *BasicBlock {
	f := b.Fn
	block := &BasicBlock{
		Index:   len(f.Blocks),
		Comment: comment,
		parent:  f,
	}
	block.Succs = block.succs2[:0]
	f.Blocks = append(f.Blocks, block)
	return block
}

// NewFunction returns a new synthetic Function instance belonging to
// prog, with its name and signature fields set as specified.
//
// The caller is responsible for initializing the remaining fields of
// the function object, e.g. Pkg, Params, Blocks.
//
// It is practically impossible for clients to construct well-formed
// SSA functions/packages/programs directly, so we assume this is the
// job of the Builder alone.  NewFunction exists to provide clients a
// little flexibility.  For example, analysis tools may wish to
// construct fake Functions for the root of the callgraph, a fake
// "reflect" package, etc.
//
// TODO(adonovan): think harder about the API here.
//
func (prog *Program) NewFunction(name string, sig *Signature, provenance string) *Function {
	return &Function{name: name, Signature: sig, Synthetic: provenance}
}
