// Copyright 2011 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// This file implements the Check function, which drives type-checking.

package types

import (
	"errors"
	"fmt"
	"go/constant"

	"github.com/mdempsky/amigo/syntax"
)

var nopos syntax.Pos

// debugging/development support
const debug = false // leave on during development

// exprInfo stores information about an untyped expression.
type exprInfo struct {
	isLhs bool // expression is lhs operand of a shift with delayed type-check
	mode  operandMode
	typ   *Basic
	val   constant.Value // constant value; or nil (if not a constant)
}

// An environment represents the environment within which an object is
// type-checked.
type environment struct {
	decl          *declInfo                 // package-level declaration whose init expression/function body is checked
	scope         *Scope                    // top-most scope for lookups
	pos           syntax.Pos                // if valid, identifiers are looked up as if at position pos (used by Eval)
	iota          constant.Value            // value of iota in a constant declaration; nil otherwise
	errpos        syntax.Pos                // if valid, identifier position of a constant with inherited initializer
	inTParamList  bool                      // set if inside a type parameter list
	sig           *Signature                // function signature if inside a function; nil otherwise
	isPanic       map[*syntax.CallExpr]bool // set of panic call expressions (used for termination check)
	hasLabel      bool                      // set if a function makes use of labels (only ~1% of functions); unused outside functions
	hasCallOrRecv bool                      // set if an expression contains a function call or channel receive operation
}

// lookup looks up name in the current environment and returns the matching object, or nil.
func (env *environment) lookup(name string) Object {
	_, obj := env.scope.LookupParent(name, env.pos)
	return obj
}

// An importKey identifies an imported package by import path and source directory
// (directory containing the file containing the import). In practice, the directory
// may always be the same, or may not matter. Given an (import path, directory), an
// importer must always return the same package (but given two different import paths,
// an importer may still return the same package by mapping them to the same package
// paths).
type importKey struct {
	path, dir string
}

// A dotImportKey describes a dot-imported object in the given scope.
type dotImportKey struct {
	scope *Scope
	name  string
}

// An action describes a (delayed) action.
type action struct {
	f    func()      // action to be executed
	desc *actionDesc // action description; may be nil, requires debug to be set
}

// If debug is set, describef sets a printf-formatted description for action a.
// Otherwise, it is a no-op.
func (a *action) describef(pos poser, format string, args ...interface{}) {
	if debug {
		a.desc = &actionDesc{pos, format, args}
	}
}

// An actionDesc provides information on an action.
// For debugging only.
type actionDesc struct {
	pos    poser
	format string
	args   []interface{}
}

// A Checker maintains the state of the type checker.
// It must be created with NewChecker.
type Checker struct {
	// package information
	// (initialized by NewChecker, valid for the life-time of checker)
	conf *Config
	ctxt *Context // context for de-duplicating instances
	pkg  *Package
	*Info
	version version                // accepted language version
	nextID  uint64                 // unique Id for type parameters (first valid Id is 1)
	objMap  map[Object]*declInfo   // maps package-level objects and (non-interface) methods to declaration info
	impMap  map[importKey]*Package // maps (import path, source directory) to (complete or fake) package
	infoMap map[*Named]typeInfo    // maps named types to their associated type info (for cycle detection)

	// pkgPathMap maps package names to the set of distinct import paths we've
	// seen for that name, anywhere in the import graph. It is used for
	// disambiguating package names in error messages.
	//
	// pkgPathMap is allocated lazily, so that we don't pay the price of building
	// it on the happy path. seenPkgMap tracks the packages that we've already
	// walked.
	pkgPathMap map[string]map[string]bool
	seenPkgMap map[*Package]bool

	// information collected during type-checking of a set of package files
	// (initialized by Files, valid only for the duration of check.Files;
	// maps and lists are allocated on demand)
	files         []*syntax.File              // list of package files
	imports       []*PkgName                  // list of imported packages
	dotImportMap  map[dotImportKey]*PkgName   // maps dot-imported objects to the package they were dot-imported through
	recvTParamMap map[*syntax.Name]*TypeParam // maps blank receiver type parameters to their type
	brokenAliases map[*TypeName]bool          // set of aliases with broken (not yet determined) types
	unionTypeSets map[*Union]*_TypeSet        // computed type sets for union types
	mono          monoGraph                   // graph for detecting non-monomorphizable instantiation loops

	firstErr error                    // first error encountered
	methods  map[*TypeName][]*Func    // maps package scope type names to associated non-blank (non-interface) methods
	untyped  map[syntax.Expr]exprInfo // map of expressions without final type
	delayed  []action                 // stack of delayed action segments; segments are processed in FIFO order
	objPath  []Object                 // path of object dependencies during type inference (for cycle reporting)
	cleaners []cleaner                // list of types that may need a final cleanup at the end of type-checking

	// environment within which the current object is type-checked (valid only
	// for the duration of type-checking a specific object)
	environment

	// debugging
	indent int // indentation for tracing
}

// addDeclDep adds the dependency edge (check.decl -> to) if check.decl exists
func (check *Checker) addDeclDep(to Object) {
	from := check.decl
	if from == nil {
		return // not in a package-level init expression
	}
	if _, found := check.objMap[to]; !found {
		return // to is not a package-level object
	}
	from.addDep(to)
}

// brokenAlias records that alias doesn't have a determined type yet.
// It also sets alias.typ to Typ[Invalid].
func (check *Checker) brokenAlias(alias *TypeName) {
	if check.brokenAliases == nil {
		check.brokenAliases = make(map[*TypeName]bool)
	}
	check.brokenAliases[alias] = true
	alias.typ = Typ[Invalid]
}

// validAlias records that alias has the valid type typ (possibly Typ[Invalid]).
func (check *Checker) validAlias(alias *TypeName, typ Type) {
	delete(check.brokenAliases, alias)
	alias.typ = typ
}

// isBrokenAlias reports whether alias doesn't have a determined type yet.
func (check *Checker) isBrokenAlias(alias *TypeName) bool {
	return alias.typ == Typ[Invalid] && check.brokenAliases[alias]
}

func (check *Checker) rememberUntyped(e syntax.Expr, lhs bool, mode operandMode, typ *Basic, val constant.Value) {
	m := check.untyped
	if m == nil {
		m = make(map[syntax.Expr]exprInfo)
		check.untyped = m
	}
	m[e] = exprInfo{lhs, mode, typ, val}
}

// later pushes f on to the stack of actions that will be processed later;
// either at the end of the current statement, or in case of a local constant
// or variable declaration, before the constant or variable is in scope
// (so that f still sees the scope before any new declarations).
// later returns the pushed action so one can provide a description
// via action.describef for debugging, if desired.
func (check *Checker) later(f func()) *action {
	i := len(check.delayed)
	check.delayed = append(check.delayed, action{f: f})
	return &check.delayed[i]
}

// push pushes obj onto the object path and returns its index in the path.
func (check *Checker) push(obj Object) int {
	check.objPath = append(check.objPath, obj)
	return len(check.objPath) - 1
}

// pop pops and returns the topmost object from the object path.
func (check *Checker) pop() Object {
	i := len(check.objPath) - 1
	obj := check.objPath[i]
	check.objPath[i] = nil
	check.objPath = check.objPath[:i]
	return obj
}

type cleaner interface {
	cleanup()
}

// needsCleanup records objects/types that implement the cleanup method
// which will be called at the end of type-checking.
func (check *Checker) needsCleanup(c cleaner) {
	check.cleaners = append(check.cleaners, c)
}

// NewChecker returns a new Checker instance for a given package.
// Package files may be added incrementally via checker.Files.
func NewChecker(conf *Config, pkg *Package, info *Info) *Checker {
	// make sure we have a configuration
	if conf == nil {
		conf = new(Config)
	}

	// make sure we have an info struct
	if info == nil {
		info = new(Info)
	}

	version, err := parseGoVersion(conf.GoVersion)
	if err != nil {
		panic(fmt.Sprintf("invalid Go version %q (%v)", conf.GoVersion, err))
	}

	return &Checker{
		conf:    conf,
		ctxt:    conf.Context,
		pkg:     pkg,
		Info:    info,
		version: version,
		objMap:  make(map[Object]*declInfo),
		impMap:  make(map[importKey]*Package),
		infoMap: make(map[*Named]typeInfo),
	}
}

// initFiles initializes the files-specific portion of checker.
// The provided files must all belong to the same package.
func (check *Checker) initFiles(files []*syntax.File) {
	// start with a clean slate (check.Files may be called multiple times)
	check.files = nil
	check.imports = nil
	check.dotImportMap = nil

	check.firstErr = nil
	check.methods = nil
	check.untyped = nil
	check.delayed = nil
	check.objPath = nil
	check.cleaners = nil

	// determine package name and collect valid files
	pkg := check.pkg
	for _, file := range files {
		switch name := file.PkgName.Value; pkg.name {
		case "":
			if name != "_" {
				pkg.name = name
			} else {
				check.error(file.PkgName, "invalid package name _")
			}
			fallthrough

		case name:
			check.files = append(check.files, file)

		default:
			check.errorf(file, "package %s; expected %s", name, pkg.name)
			// ignore this file
		}
	}
}

// A bailout panic is used for early termination.
type bailout struct{}

func (check *Checker) handleBailout(err *error) {
	switch p := recover().(type) {
	case nil, bailout:
		// normal return or early exit
		*err = check.firstErr
	default:
		// re-panic
		panic(p)
	}
}

// Files checks the provided files as part of the checker's package.
func (check *Checker) Files(files []*syntax.File) error { return check.checkFiles(files) }

var errBadCgo = errors.New("cannot use FakeImportC and go115UsesCgo together")

func (check *Checker) checkFiles(files []*syntax.File) (err error) {
	if check.conf.FakeImportC && check.conf.UsesCgo {
		return errBadCgo
	}

	defer check.handleBailout(&err)

	print := func(msg string) {
		if check.conf.Trace {
			fmt.Println()
			fmt.Println(msg)
		}
	}

	print("== initFiles ==")
	check.initFiles(files)

	print("== collectObjects ==")
	check.collectObjects()

	print("== packageObjects ==")
	check.packageObjects()

	print("== processDelayed ==")
	check.processDelayed(0) // incl. all functions

	print("== cleanup ==")
	check.cleanup()

	print("== initOrder ==")
	check.initOrder()

	if !check.conf.DisableUnusedImportCheck {
		print("== unusedImports ==")
		check.unusedImports()
	}

	print("== recordUntyped ==")
	check.recordUntyped()

	if check.firstErr == nil {
		// TODO(mdempsky): Ensure monomorph is safe when errors exist.
		check.monomorph()
	}

	check.pkg.complete = true

	// no longer needed - release memory
	check.imports = nil
	check.dotImportMap = nil
	check.pkgPathMap = nil
	check.seenPkgMap = nil
	check.recvTParamMap = nil
	check.brokenAliases = nil
	check.unionTypeSets = nil
	check.ctxt = nil

	// TODO(gri) There's more memory we should release at this point.

	return
}

// processDelayed processes all delayed actions pushed after top.
func (check *Checker) processDelayed(top int) {
	// If each delayed action pushes a new action, the
	// stack will continue to grow during this loop.
	// However, it is only processing functions (which
	// are processed in a delayed fashion) that may
	// add more actions (such as nested functions), so
	// this is a sufficiently bounded process.
	for i := top; i < len(check.delayed); i++ {
		a := &check.delayed[i]
		if check.conf.Trace {
			if a.desc != nil {
				check.trace(a.desc.pos.Pos(), "-- "+a.desc.format, a.desc.args...)
			} else {
				check.trace(nopos, "-- delayed %p", a.f)
			}
		}
		a.f() // may append to check.delayed
		if check.conf.Trace {
			fmt.Println()
		}
	}
	assert(top <= len(check.delayed)) // stack must not have shrunk
	check.delayed = check.delayed[:top]
}

// cleanup runs cleanup for all collected cleaners.
func (check *Checker) cleanup() {
	// Don't use a range clause since Named.cleanup may add more cleaners.
	for i := 0; i < len(check.cleaners); i++ {
		check.cleaners[i].cleanup()
	}
	check.cleaners = nil
}

func (check *Checker) record(x *operand) {
	// convert x into a user-friendly set of values
	// TODO(gri) this code can be simplified
	var typ Type
	var val constant.Value
	switch x.mode {
	case invalid:
		typ = Typ[Invalid]
	case novalue:
		typ = (*Tuple)(nil)
	case constant_:
		typ = x.typ
		val = x.val
	default:
		typ = x.typ
	}
	assert(x.expr != nil && typ != nil)

	if isUntyped(typ) {
		// delay type and value recording until we know the type
		// or until the end of type checking
		check.rememberUntyped(x.expr, false, x.mode, typ.(*Basic), val)
	} else {
		check.recordTypeAndValue(x.expr, x.mode, typ, val)
	}
}

func (check *Checker) recordUntyped() {
	if !debug && check.Types == nil {
		return // nothing to do
	}

	for x, info := range check.untyped {
		if debug && isTyped(info.typ) {
			check.dump("%v: %s (type %s) is typed", posFor(x), x, info.typ)
			unreachable()
		}
		check.recordTypeAndValue(x, info.mode, info.typ, info.val)
	}
}

func (check *Checker) recordTypeAndValue(x syntax.Expr, mode operandMode, typ Type, val constant.Value) {
	assert(x != nil)
	assert(typ != nil)
	if mode == invalid {
		return // omit
	}
	if mode == constant_ {
		assert(val != nil)
		// We check allBasic(typ, IsConstType) here as constant expressions may be
		// recorded as type parameters.
		assert(typ == Typ[Invalid] || allBasic(typ, IsConstType))
	}
	if m := check.Types; m != nil {
		m[x] = TypeAndValue{mode, typ, val}
	}
}

func (check *Checker) recordBuiltinType(f syntax.Expr, sig *Signature) {
	// f must be a (possibly parenthesized, possibly qualified)
	// identifier denoting a built-in (including unsafe's non-constant
	// functions Add and Slice): record the signature for f and possible
	// children.
	for {
		check.recordTypeAndValue(f, builtin, sig, nil)
		switch p := f.(type) {
		case *syntax.Name, *syntax.SelectorExpr:
			return // we're done
		case *syntax.ParenExpr:
			f = p.X
		default:
			unreachable()
		}
	}
}

func (check *Checker) recordCommaOkTypes(x syntax.Expr, a [2]Type) {
	assert(x != nil)
	if a[0] == nil || a[1] == nil {
		return
	}
	assert(isTyped(a[0]) && isTyped(a[1]) && (isBoolean(a[1]) || a[1] == universeError))
	if m := check.Types; m != nil {
		for {
			tv := m[x]
			assert(tv.Type != nil) // should have been recorded already
			pos := x.Pos()
			tv.Type = NewTuple(
				NewVar(pos, check.pkg, "", a[0]),
				NewVar(pos, check.pkg, "", a[1]),
			)
			m[x] = tv
			// if x is a parenthesized expression (p.X), update p.X
			p, _ := x.(*syntax.ParenExpr)
			if p == nil {
				break
			}
			x = p.X
		}
	}
}

// recordInstance records instantiation information into check.Info, if the
// Instances map is non-nil. The given expr must be an ident, selector, or
// index (list) expr with ident or selector operand.
//
// TODO(rfindley): the expr parameter is fragile. See if we can access the
// instantiated identifier in some other way.
func (check *Checker) recordInstance(expr syntax.Expr, targs []Type, typ Type) {
	ident := instantiatedIdent(expr)
	assert(ident != nil)
	assert(typ != nil)
	if m := check.Instances; m != nil {
		m[ident] = Instance{newTypeList(targs), typ}
	}
}

func instantiatedIdent(expr syntax.Expr) *syntax.Name {
	var selOrIdent syntax.Expr
	switch e := expr.(type) {
	case *syntax.IndexExpr:
		selOrIdent = e.X
	case *syntax.SelectorExpr, *syntax.Name:
		selOrIdent = e
	}
	switch x := selOrIdent.(type) {
	case *syntax.Name:
		return x
	case *syntax.SelectorExpr:
		return x.Sel
	}
	panic("instantiated ident not found")
}

func (check *Checker) recordDef(id *syntax.Name, obj Object) {
	assert(id != nil)
	if m := check.Defs; m != nil {
		m[id] = obj
	}
}

func (check *Checker) recordUse(id *syntax.Name, obj Object) {
	assert(id != nil)
	assert(obj != nil)
	if m := check.Uses; m != nil {
		m[id] = obj
	}
}

func (check *Checker) recordImplicit(node syntax.Node, obj Object) {
	assert(node != nil)
	assert(obj != nil)
	if m := check.Implicits; m != nil {
		m[node] = obj
	}
}

func (check *Checker) recordSelection(x *syntax.SelectorExpr, kind SelectionKind, recv Type, obj Object, index []int, indirect bool) {
	assert(obj != nil && (recv == nil || len(index) > 0))
	check.recordUse(x.Sel, obj)
	if m := check.Selections; m != nil {
		m[x] = &Selection{kind, recv, obj, index, indirect}
	}
}

func (check *Checker) recordScope(node syntax.Node, scope *Scope) {
	assert(node != nil)
	assert(scope != nil)
	if m := check.Scopes; m != nil {
		m[node] = scope
	}
}
