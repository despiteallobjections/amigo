# Build systems

Amigo aims to support two build systems, or at least styles there of:
cmd/go and Bazel(+Gazelle).

The key distinction of these two build systems is when package
discovery happens. E.g., the user invokes a command to build a
particular target; how does the build system discover which packages
to build, and which source files define those packages for the target
configuration?

## cmd/go

cmd/go is a dynamic discovery system. When the user types `go build
my/project`, it recursively:

1. Finds `my/project`'s source directory (whether on disk, or
   implicitly in the module cache).
2. Applies build tag filtering to identify which source files are
   actually relevant to the target configuration (e.g., `GOOS`,
   `GOARCH`, `GOEXPERIMENT`).
3. Partially parses the source files to identify which other packages
   are imported. This includes resolving vendored import paths.
4. For each imported package, the entire process is recursively (and
   concurrently) applied.
5. Compilation of this package waits until all imported packages are
   up-to-date.
6. Invokes the compiler to build the package from the source files and
   imported packages' compiler artifacts.
7. If `my/project` specifies a main package, invokes the linker to
   build the final executable.

## Bazel and Gazelle

Bazel instead follows a static build graph model, where all build
actions are declared in BUILD.bzl files. The Gazelle tool is available
to simplify this process, by inspecting source files and automatically
regenerating BUILD.bzl files.

In effect, Gazelle handles steps 1--4, except it has to simultaneously
allow for all possible target configurations. Bazel then handles just
steps 5--7.
