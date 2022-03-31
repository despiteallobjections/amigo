# Parallelism

## Abstract

This doc elaborates on amigo's hypothesis for improving parallelism
during analysis and compilation of Go code.

## Background

### Tools

Today, the gc toolchain suite includes a few tools:

* cmd/go: The overall build orchestration tool. The cmd/go tool is how
  most users interact with the toolchain. It handles tasks like
  interpreting user commands (`go build std`), locating source files
  (incl. knowing that `GOOS=linux` builds should skip `*_windows.go`
  source files), analyzing package dependencies, sequencing invocation
  of other tools (e.g., package fmt depends on package reflect, so
  reflect has to finish compiling before we can start compliing
  package fmt), and caching results to minimize redundant work.

* cmd/compile: The Go compiler. The cmd/compile tool handles
  compilation of a single Go package. It's given a list of Go source
  files to parse and type check, and a configuration file that
  specifies how to handle `import` declarations (i.e., how to resolve
  local and vendored import paths, and where to find the compiler
  artifacts for those imported packages). It's primary result is
  writing out the compiler and linker artifacts, described further in
  the next section.

* cmd/link: The Go linker. The cmd/link tool reads all of the linker
  artifacts created by cmd/compile, and writes out the final
  executable file. (Due to go.dev/s/buildmodes, sometimes the output
  file is actually a DSO or linkable archive file; but these details
  aren't relevant here.)

* cmd/asm: The Go assembler. The gc toolchain defines its own assembly
  language dialect, which is mostly used within the runtime and
  several performance-critical bits of code (e.g., byte/string
  manipulation, math/big, and crypto). The details aren't terribly
  important, except to note that it exists and is a critical part of
  building the Go standard library.

* cmd/cgo: The source-to-source translation tool for supporting
  Cgo. The cmd/cgo tool parses Go source code, identifies `import "C"`
  declarations and uses of `C.xxx` identifiers, and then invokes the C
  compiler and analyzes the results so that it can eventually mangle
  the user source into standard Go source that can be handled by
  cmd/compile.

### Build artifacts

Separate compilation of Go packages is handled through the use of two
kinds of build artifacts:

* Compiler artifacts, also commonly known as "export data files". On
  disk (at least within their respective pack file), these files are
  typically named `__.PKGDEF`.

  These artifacts contain typing information about their respective
  source package and its exported declarations, which are used by
  subsequent cmd/compile invocations to handle `import`
  declarations. They're also used for the same purpose by
  go/types.Importer implementations (e.g., go/internal/gcimporter and
  x/tools/go/gcexportdata).

  Today the files are self-contained: if package B's exported
  declarations refer to a type from package A, package B's export data
  will "re-export" that type declaration from package A.

  The file also contains some compiler-specific optimization details,
  like ininable function bodies and escape analysis summaries. These
  details are ignored by go/types.Importer implementations.

* Linker artifacts. These files are similar to traditional UNIX object
  file, with symbols, definitions, and relocations. For compiled
  functions, the symbol definitions will be machine instructions
  suitable for execution by the target CPU.

  cmd/compile is the main producer of linker artifacts, which always
  names them `_go_.o`. But packages that contain Go assembly code will
  have additional linker artifacts produced by cmd/asm.

  cmd/link is the main consumer of linker artifacts. The cmd/nm and
  cmd/objdump tools can also analyze them, but these tools exist
  primarily for use by the Go toolchain developers ourselves.

The gc toolchain is a complete system, and users must use a fully
matched tool suite. E.g., the Go 1.18 compiler only supports reading
its own compiler artifacts, and the Go 1.18 linker only supports
reading linker artifacts from the Go 1.18 compiler.

The one important exception here is that x/tools/go/gcexportdata is
versioned separated from the gc toolchain, and it intentionally
supports reading export data from many past Go compiler releases.
Notably, this complicates evolving the export data format.

## Limited parallelism

As mentioned, cmd/compile is responsible for writing out two build
artifacts, and cmd/go currently waits for cmd/compile to finish
writing both of them before allowing subsequent build steps to start.
If package B depends on package A, then cmd/compile has to finish
writing out both build artifacts for package A, before it can start on
package B.

Unfortunately, this design artificially limits build parallelism: to
compile package B, cmd/compile only needs package A's compiler
artifact. But currently we have to wait for cmd/compile to finish
creating package A's linker artifact anyway.

Moreover, cmd/compile typically spends the vast majority of its
execution time on creating linker artifacts, not compiler
artifacts. Type checking the package's top-level declarations (which
is necessary for writing out export data) is relatively very fast;
while type checking function bodies, creating and optimizing SSA
representations of the function bodies, and finally assembling to
machine instructions is relatively much, much slower.

### Example: `go build -a -v std`

A notable example of the current limited parallelism is if you run `go
build -a -v std` (i.e., re-build the entire standard library without
caching, and print packages as they're compiled).

Even though there's tons of packages to compile, you'll almost always
notice a small stutter in output near the beginning, shortly after
"runtime" is printed. This is because a lot of packages depend on
package runtime, and it has a very large linker object. So the entire
build graph stalls waiting for package runtime's linker object, even
though `go build -a -v std` never even invokes cmd/link.

## Solution

The problem is dependency analysis between build steps is too coarse
grained. Ideally, we want to minimize how much work happens along the
critical path of package dependencies.

At a minimum, we need to split cmd/compile into two steps: one that
writes out the compiler artifact, and a separate that writes out the
linker artifact.

Longer term, I can imagine more than two steps. For example, the
compiler artifact currently includes some compiler-specific
optimization details that are necessary for creating (optimized)
linker artifacts, but aren't needed for type checking.

Perhaps instead we split the "compiler artifact" into the
"type-checker artifact" and the "inter-package optimization artifact",
with additional phases for producing these artifacts.

## Prior art

Java has similar build dependency issues, which Google's Javac Team
has experience optimizing around. The current state of art there is
Turbine, which is available at https://github.com/google/turbine.

A design doc for Turbine is available to Googlers at
go/java-header-compilation. I've asked the Javac Team if there are any
publicly available copies of this documentation.
