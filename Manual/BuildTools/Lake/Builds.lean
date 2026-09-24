/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Command
import Lake.Build.Package
import Lake.Build.Library
import Lake.Build.Module

import Manual.Meta

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option guard_msgs.diff true

#doc (Manual) "Builds" =>
%%%
tag := "lake-builds"
%%%

:::paragraph
Producing a desired {tech}[artifact], such as a {tech}[`.olean` file] or an executable binary, is called a {deftech}_build_.
Builds are triggered by the {lake}`build` command or by other commands that require an artifact to be present, such as {lake}`exe`.
A build consists of the following steps:

: {deftech (key := "configure package")}[Configuring] the package

  If {tech}[package configuration] file is newer than the cached configuration file `lakefile.olean`, then the package configuration is re-elaborated.
  This also occurs when the cached file is missing or when the {lakeOpt}`--reconfigure` or {lakeOpt}`-R` flag is provided.
  Changes to options using {lakeOpt}`-K` do not trigger re-elaboration of the configuration file; {lakeOpt}`-R` is necessary in these cases.

: Computing dependencies

  The set of artifacts that are required to produce the desired output are determined, along with the {tech}[targets] and {tech}[facets] that produce them.
  This process is recursive, and the result is a _graph_ of dependencies.
  The dependencies in this graph are distinct from those declared for a package: packages depend on other packages, while build targets depend on other build targets, which may be in the same package or in a different one.
  One facet of a given target may depend on other facets of the same target.
  Lake automatically analyzes the imports of Lean modules to discover their dependencies, and the {tomlField Lake.LeanLibConfig}`extraDepTargets` field can be used to add additional dependencies to a target.

: Replaying traces

  Rather than rebuilding everything in the dependency graph from scratch, Lake uses saved {deftech}_trace files_ to determine which artifacts require building.
  During a build, Lake records which source files or other artifacts were used to produce each artifact, saving a hash of each input; these {deftech}_traces_ are saved in the {tech}[build directory].{margin}[More specifically, each artifact's trace file contains a Merkle tree hash mixture of its inputs' hashes.]
  If the inputs are all unmodified, then the corresponding artifact is not rebuilt.
  Trace files additionally record the {tech}[log] from each build task; these outputs are replayed as if the artifact had been built anew.
  Reusing prior build products when possible is called an {deftech}_incremental build_.

: Building artifacts

  When all unmodified dependencies in the dependency graph have been replayed from their trace files, Lake proceeds to build each artifact.
  This involves running the appropriate build tool on the input files and saving the artifact and its trace file, as specified in the corresponding facet.
:::

Lake uses two separate hash algorithms.
Text files are hashed after normalizing newlines, so that files that differ only by platform-specific newline conventions are hashed identically.
Other files are hashed without any normalization.

Along with the trace files, Lean caches input hashes.
Whenever an artifact is built, its hash is saved in a separate file that can be re-read instead of computing the hash from scratch.
This is a performance optimization.
This feature can be disabled, causing all hashes to be recomputed from their inputs, using the {lakeOpt}`--rehash` command-line option.

:::paragraph
During a build, the following directories are provided to the underlying build tools:
 * The {deftech}_source directory_ contains Lean source code that is available for import.
 * The {deftech}_library directories_ contain {tech}[`.olean` files] along with the shared and static libraries that are available for linking; it normally consists of the {tech}[root package]'s library directory (found in `.lake/build/lib`), the library directories for the other packages in the workspace, the library directory for the current Lean toolchain, and the system library directory.
 * The {deftech}_Lake home_ is the directory in which Lake is installed, including binaries, source code, and libraries.
   The libraries in the Lake home are needed to elaborate Lake configuration files, which have access to the full power of Lean.
:::

# Facets
%%%
tag := "lake-facets"
%%%

A {deftech}_facet_ describes the production of a target from another.
Conceptually, any target may have facets.
However, executables, external libraries, and custom targets provide only a single implicit facet.
Packages, libraries, and modules have multiple facets that can be requested by name when invoking {lake}`build` to select the corresponding target.

When no facet is explicitly requested, but an initial target is designated, {lake}`build` produces the initial target's {deftech}_default facet_.
Each type of initial target has a corresponding default facet (e.g. producing an executable binary from an executable target or building a package's {tech}[default targets]); other facets may be explicitly requested in the {tech}[package configuration] or via Lake's {ref "lake-cli"}[command-line interface].
Lake's internal API may be used to write custom facets.


```lakeHelp "build"
Build targets

USAGE:
  lake build [<targets>...] [-o <mappings>] [--package <name>]

A target is specified with a string of the form:

  [@[<package>]/][<target>|[+]<module>][:<facet>]

You can also use the source path of a module as a target. For example,

  lake build Foo/Bar.lean:o

will build the Lean module (within the workspace) whose source file is
`Foo/Bar.lean` and compile the generated C file into a native object file.

The `@` and `+` markers can be used to disambiguate packages and modules
from file paths or other kinds of targets (e.g., executables or libraries).

LIBRARY FACETS:         build the library's ...
  elabArts              elaboration artifacts (*.olean, *.ilean files)
  irArts (default)      compilation artifacts (*.ir, *.ir.sig, *.c files)
  static                static artifact (*.a file)
  shared                shared artifact (*.so, *.dll, or *.dylib file)

MODULE FACETS:          build the module's ...
  deps                  dependencies (e.g., imports, shared libraries, etc.)
  elabArts              elaboration artifacts (*.olean, *.ilean files)
  irArts (default)      compilation artifacts (*.ir, *.ir.sig, *.c files)
  olean                 OLean (binary blob of Lean data for importers)
  ilean                 ILean (binary blob of metadata for the Lean LSP server)
  c                     compiled C file
  bc                    compiled LLVM bitcode file
  c.o                   compiled object file (of its C file)
  bc.o                  compiled object file (of its LLVM bitcode file)
  o                     compiled object file (of its configured backend)
  dynlib                shared library (e.g., for `--load-dynlib`)

TARGET EXAMPLES:        build the ...
  a                     default facet(s) of target `a`
  @a                    default target(s) of package `a`
  +A                    default facet(s) of module `A`
  @/a                   default facet(s) of target `a` of the root package
  @a/b                  default facet(s) of target `b` of package `a`
  @a/+A:c               C file of module `A` of package `a`
  :foo                  facet `foo` of the root package

A bare `lake build` command will build the default target(s) of the root
package. Package dependencies are not updated during a build.

With the Lake cache enabled, Lake can track the targets the build covers
(both those up-to-date and those newly built) and write the input-to-outputs
mappings of each to a file specified by the `-o` option. By default, with `-o`,
Lake will track the targets of the root package, use `--package` to select a
different one. These mappings can then be used to upload the build artifacts
to a remote cache with `lake cache put`. This will only include the artifacts
from the covered targets. Other targets in the package will not be tracked.
```


::::paragraph

The facets available for packages are:

```lean -show
-- Always keep this in sync with the description below. It ensures that the list is complete.
/--
info: #[`package.barrel, `package.cache, `package.defaultModules, `package.deps, `package.extraDep, `package.optBarrel,
  `package.optCache, `package.optRelease, `package.release, `package.transDeps]
-/
#guard_msgs in
#eval Lake.initPackageFacetConfigs.toList.map (·.1) |>.toArray |>.qsort (·.toString < ·.toString)
```
: `extraDep`

  The default facets of the package's extra dependency targets, specified in the {tomlField Lake.PackageConfig}`extraDepTargets` field.

: `deps`

  The package's {tech}[direct dependencies].

: `transDeps`

  The package's {tech}[transitive dependencies], topologically sorted.

: `defaultModules`

  The Lean modules of the package's {tech}[default targets]: every module of each default library, and the root module of each default executable together with the modules it transitively imports from the workspace.
  Other default targets, such as {ref "lake-config-custom-target"}[custom targets], are not included.


: `optCache`

  A package's optional cached build archive (e.g., from Reservoir or GitHub).
  Will *not* cause the whole build to fail if the archive cannot be fetched.

: `cache`

  A package's cached build archive (e.g., from Reservoir or GitHub).
  Will cause the whole build to fail if the archive cannot be fetched.

: `optBarrel`

  A package's optional cached build archive (e.g., from Reservoir or GitHub).
  Will *not* cause the whole build to fail if the archive cannot be fetched.

: `barrel`

  A package's cached build archive (e.g., from Reservoir or GitHub).
  Will cause the whole build to fail if the archive cannot be fetched.

: `optRelease`

  A package's optional build archive from a GitHub release.
  Will *not* cause the whole build to fail if the release cannot be fetched.

: `release`

  A package's build archive from a GitHub release.
  Will cause the whole build to fail if the archive cannot be fetched.


::::

```lean -show
-- Always keep this in sync with the description below. It ensures that the list is complete.
/--
info: [`lean_lib.elabArts, `lean_lib.extraDep, `lean_lib.leanArts, `lean_lib.irArts, `lean_lib.static.export,
  `lean_lib.shared, `lean_lib.modules, `lean_lib.static, `lean_lib.default]
-/
#guard_msgs in
#eval Lake.initLibraryFacetConfigs.toList.map (·.1)
```

:::paragraph

The facets available for libraries are:

: `elabArts`

  The library's elaboration artifacts (`*.olean` and `*.ilean` files).

: `irArts` (default)

  The library's code-generation artifacts (`*.ir`, `*.ir.sig`, and `*.c` files).

: `leanArts`

  The artifacts that the Lean compiler produces for the library or executable ({tech (key := ".olean files")}`*.olean`, `*.ilean`, and `*.c` files).

: `static`

  The static library produced by the C compiler from the `leanArts` (that is, a `*.a` file).

: `static.export`

  The static library produced by the C compiler from the `leanArts` (that is, a `*.a` file), with exported symbols.

: `shared`

  The shared library produced by the C compiler from the `leanArts` (that is, a `*.so`, `*.dll`, or `*.dylib` file, depending on the platform).

: `extraDep`

  A Lean library's {tomlField Lake.LeanLibConfig}`extraDepTargets` and those of its package.

:::

:::paragraph

Executables have a single `exe` facet that consists of the executable binary.

:::

```lean -show
-- Always keep this in sync with the description below. It ensures that the list is complete.
/--
info: module.bc
module.bc.o
module.c
module.c.o
module.c.o.export
module.c.o.noexport
module.depHash
module.depTrace
module.deps
module.dynlib
module.elabArts
module.exportInfo
module.header
module.ilean
module.importAllArts
module.importArts
module.importInfo
module.imports
module.input
module.ir
module.ir.sig
module.irArts
module.lean
module.leanArts
module.linkInfoExport
module.linkInfoNoExport
module.ltar
module.metaExportInfo
module.o
module.o.export
module.o.noexport
module.olean
module.olean.private
module.olean.server
module.precompileImports
module.presetup
module.setup
module.transImports
-/
#guard_msgs in
#eval Lake.initModuleFacetConfigs.toList.toArray.map (·.1) |>.qsort (·.toString < ·.toString) |>.forM (IO.println)
```

:::paragraph
The facets available for modules are:

: `lean`

  The module's Lean source file.

: `elabArts`

 The module's elaboration artifacts (`*.olean` and `*.ilean` files).

: `irArts` (default)

 The module's code-generation artifacts (`*.ir`, `*.ir.sig`, and `*.c` files).

: `leanArts`

 All artifacts produced by elaboration and code generation.

: `deps`

  The module's dependencies (e.g., imports or shared libraries).

: `depHash`

  A hash of a module's build dependencies (e.g., imports, source, plugins).

: `depTrace`

  A Lake build trace data structure (i.e., composite hash and modification time) of a module's build dependencies (e.g., imports, source, plugins).

: `olean`

 The module's {tech}[`.olean` file]. {TODO}[Once module system lands fully, add docs for `olean.private` and `olean.server`]

: `ilean`

 The module's `.ilean` file, which is metadata used by the Lean language server.

: `header`

  The parsed module header of the module's source file.

: `input`

  The module's processed Lean source file. Combines tracing the file with parsing its header.

: `imports`

  The immediate imports of the Lean module, but not the full set of transitive imports. {TODO}[Once the module system lands fully, add docs here for `module.importAllArts`, `module.importArts`]

: `precompileImports`

  The transitive imports of the Lean module, compiled to object code.

: `transImports`

  The transitive imports of the Lean module, as {tech}[`.olean` files].

: `allImports`

  Both the immediate and transitive imports of the Lean module.

: `setup`

  All of a module's dependencies: transitive local imports and shared libraries to be loaded with `--load-dynlib`.
  Returns the list of shared libraries to load along with their search path.

: `ir`

  The `.ir` file produced for modules that use the {ref "module-structure"}[module system].


: `ir.sig`

  The `.ir.sig` file produced for modules that use the {ref "module-structure"}[module system].

: `c`

 The C file produced by the Lean compiler.

: `bc`

 LLVM bitcode file, produced by the Lean compiler.

: `c.o`

 The compiled object file, produced from the C file. On Windows, this is equivalent to `.c.o.noexport`, while it is equivalent to `.c.o.export` on other platforms.

: `c.o.export`

 The compiled object file, produced from the C file, with Lean symbols exported.

: `c.o.noexport`

 The compiled object file, produced from the C file, without Lean symbols exported.

: `bc.o`

 The compiled object file, produced from the LLVM bitcode file.

: `o`

 The compiled object file for the configured backend.

: `dynlib`

  A shared library (e.g., for the Lean option `--load-dynlib`){TODO}[Document Lean command line options, and cross-reference from here].

: `ltar`

  A compressed archive (produced via `leantar`) of the module's build artifacts. {TODO}[Document `leantar` in the manual as well]

: `linkInfoExport`

  A structured representation of the linker arguments, static objects, and dynamic libraries needed to link a module and its dependencies. Objects have Lean symbols exported.

: `linkInfoNoExport`

  A structured representation of the linker arguments, static objects, and dynamic libraries needed to link a module and its dependencies. Objects do not Lean symbols exported.

:::
