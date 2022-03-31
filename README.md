# Amigo

[![Go](https://github.com/mdempsky/amigo/actions/workflows/go.yml/badge.svg)](https://github.com/mdempsky/amigo/actions/workflows/go.yml)

Amigo is an experiment to radically reinvision the Go tools ecosystem,
including cmd/compile, cmd/vet, x/tools/gopls, and users of the go/*
and x/tools/go/* APIs.

## Hypotheses

Every proper experiment starts with declaring its hypotheses in
advance, and amigo is no exception.

1. Replace trees with tapes. The simdjson project demonstrates the
   performance benefit of parsing files into minimally structured
   token sequences, and then implementing a cursor API on top.
   Similarly, flatbuffers demonstrate the value of simply mapping data
   files into memory and walking them as-is, rather than trying to
   parse into traditional (sparse) data structures. I anticipate we
   can see similar benefits with parsing and traversing Go syntax.

2. Opaque internal data structures. The go/types type checker suffers
   from the Go 1 compatibility guarantee: APIs like go/ast and
   go/types must remain backwards compatible for existing users, which
   constrains how they can be extended to support new Go language
   features. This results in monotonically increasing implementation
   complexity, and in turn maintainer anxiety in deciding how to
   extend existing APIs.

3. First-class serialization. Today, Go tools frequently re-parse
   source files and re-type-check source packages. The compiler's
   "Unified IR" experiment demonstrates the benefit of serializing to
   bytes right away, and then developing multiple readers that can
   inflate the results into tool-appropriate data structures.

4. Build SSA during type checking. Today, the type checker walks the
   AST, disambiguates various syntactic forms, and records a bunch of
   typing information; and then the SSA builders need to re-walk the
   same AST, disambiguate the same syntactic forms, and lookup all the
   recorded typing information. I anticipate that by incorporating SSA
   construction directly into type checking, we can reduce code
   complexity and improve performance (e.g., through better memory
   locality).

5. Separate phases to improve concurrency. A typical Go build involves
   compiling each package in the dependency graph, and a package
   cannot be compiled until all of its dependencies have been compiled
   first. However, within cmd/compile, each compilation is internally
   split into a sequence of phases, and not all phases actually affect
   dependent packages. For example, (fully) type checking a package
   only requires having type checked all imported package's
   package-scope declarations; it does not require type checking
   function bodies, much less compiling and optimizing to machine
   instructions. By better defining these separate phases and the data
   flow between them, I anticipate we could further improve build
   concurrency.

   This hypothesis is further elaborated in doc/parallelism.md.

## Questions

### cmd/asm

Should amigo incorporate cmd/asm/asm too? I think yes, but cmd/asm
seems especially challenging to incorporate, without pulling in all of
cmd/internal/obj.

I suspect something like LLVM bitstream's "abbreviations" will be
applicable here. For each unique instruction shape, we can define a
separate abbreviation, so that instructions themselves can be very
efficiently encoded, and the cmd/asm decoder can use vtables to
rapidly construct obj.Progs (or report errors) from the encoded
instructions.
