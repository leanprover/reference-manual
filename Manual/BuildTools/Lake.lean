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
import Manual.BuildTools.Lake.CLI
import Manual.BuildTools.Lake.Config

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option guard_msgs.diff true

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "Lake" =>
%%%
tag := "lake"
%%%

Lake is the standard Lean build tool.
It is responsible for:
 * Configuring builds and building Lean code
 * Fetching and building external dependencies
 * Integrating with Reservoir, the Lean package server
 * Running tests, linters, and other development workflows

Lake is extensible.
It provides a rich API that can be used to define incremental build tasks for software artifacts that are not written in Lean, to automate administrative tasks, and to integrate with external workflows.
For build configurations that do not need these features, Lake provides a declarative configuration language that can be written either in TOML or as a Lean file.

This section describes Lake's {ref "lake-cli"}[command-line interface], {ref "lake-config"}[configuration files], and {ref "lake-api"}[internal API].
All three share a set of concepts and terminology.


# Concepts and Terminology
%%%
tag := "lake-vocab"
%%%

A {deftech}_package_ is the basic unit of Lean code distribution.
A single package may contain multiple libraries or executable programs.
A package consist of a directory that contains a {tech}[package configuration] file together with source code.
Packages may {deftech}_require_ other packages, in which case those packages' code (more specifically, their {tech}[targets]) are made available.
The {deftech}_direct dependencies_ of a package are those that it requires, and the {deftech}_transitive dependencies_ are the direct dependencies of a package together with their transitive dependencies.
Packages may either be obtained from [Reservoir](https://reservoir.lean-lang.org/){TODO}[xref chapter], the Lean package repository, or from a manually-specified location.
{deftech}_Git dependencies_ are specified by a Git repository URL along with a revision (branch, tag, or hash) and must be cloned locally prior to build, while local {deftech}_path dependencies_ are specified by a path relative to the package's directory.

:::paragraph
A {deftech}_workspace_ is a directory on disk that contains a working copy of a {tech}[package]'s source code and the source code of all {tech}[transitive dependencies] that are not specified as local paths.
The package for which the workspace was created is the {deftech}_root package_.
The workspace also contains any built {tech}[artifacts] for the package, enabling {tech}[incremental builds].
Dependencies and artifacts do not need to be present for a directory to be considered a workspace; commands such as {lake}`update` and {lake}`build` produce them if they are missing.
Lake is typically used in a workspace.{margin}[{lake}`init` and {lake}`new`, which create workspaces, are exceptions.]
Workspaces typically have the following layout:

 * `lean-toolchain` - The {tech}[toolchain file].
 * `lakefile.toml` or `lakefile.lean` - The {tech}[package configuration] file for the root package.
 * `lake-manifest.json` - The root package's {tech}[manifest].
 * `.lake/` - Intermediate state managed by Lake, such as built {tech}[artifacts] and dependency source code.
   * `.lake/lakefile.olean` - The root package's configuration, cached.
   * `.lake/packages/` - The workspace's {deftech}_package directory_, which contains copies of all non-local transitive dependencies of the root package, with their built artifacts in their own `.lake` directories.
   * `.lake/build/` - The {deftech}_build directory_, which contains built artifacts for the root package:
     * `.lake/build/bin` - The package's {deftech}_binary directory_, which contains built executables.
     * `.lake/build/lib` - The package's _library directory_, which contains built libraries and {tech}[`.olean` files].
     * `.lake/build/ir` - The package's intermediate result directory, which contains generated intermediate artifacts, primarily C code.
:::

:::figure "Workspace Layout" (tag :="workspace-layout")
![Lake Workspaces](/static/figures/lake-workspace.svg)
:::

:::paragraph
A {deftech}_package configuration_ file specifies the dependencies, settings, and targets of a package.
Packages can specify configuration options that apply to all their contained targets.
They can be written in two formats:
 * The {ref "lake-config-toml"}[TOML format] (`lakefile.toml`) is used for fully declarative package configurations.
 * The {ref "lake-config-lean"}[Lean format] (`lakefile.lean`) additionally supports the use of Lean code to configure the package in ways not supported by the declarative options.
:::

A {deftech}_manifest_ tracks the specific versions of other packages that are used in a package.
Together, a manifest and a {tech}[package configuration] file specify a unique set of transitive dependencies for the package.
Before building, Lake synchronizes the local copy of each dependency with the version specified in the manifest.
If no manifest is available, Lake fetches the latest matching versions of each dependency and creates a manifest.
It is an error if the package names listed in the manifest do not match those used by the package; the manifest must be updated using {lake}`update` prior to building.
Manifests should be considered part of the package's code and should normally be checked into source control.

:::paragraph
A {deftech}_target_ represents an output that can be requested by a user.
A persistent build output, such as object code, an executable binary, or an {tech}[`.olean` file], is called an {deftech}_artifact_.
In the process of producing an artifact, Lake may need to produce further artifacts; for example, compiling a Lean program into an executable requires that it and its dependencies be compiled to object files, which are themselves produced from C source files, which result from elaborating Lean sourcefiles and producing {tech}[`.olean` files].
Each link in this chain is a target, and Lake arranges for each to be built in turn.
At the start of the chain are the {deftech}_initial targets_:
 * {tech}_Packages_ are units of Lean code that are distributed as a unit.
 * {deftech}_Libraries_ are collections of Lean {tech}[module]s, organized hierarchically under one or more {deftech}_module roots_.
 * {deftech}_Executables_ consist of a _single_ module that defines `main`.
 * {deftech}_External libraries_ are non-Lean *static* libraries that will be linked to the binaries of the package and its dependents, including both their shared libraries and executables.
 * {deftech}_Custom targets_ contain arbitrary code to run a build, written using Lake's internal API.

In addition to their Lean code, packages, libraries, and executables contain configuration settings that affect subsequent build steps.
Packages may specify a set of {deftech}_default targets_.
Default targets are the initial targets in the package that are to be built in contexts where a package is specified but specific targets are not.
:::

:::paragraph
The {deftech}_log_ contains information produced during a build.
Logs are saved so they can be replayed during {tech}[incremental builds].
Messages in the log have four levels, ordered by severity:

 1. _Trace messages_ contain internal build details that are often specific to the machine on which the build is running, including the specific invocations of Lean and other tools that are passed to the shell.
 2. _Informational messages_ contain general informational output that is not expected to indicate a problem with the code, such as the results of a {keywordOf Lean.Parser.Command.eval}`#eval` command.
 3. _Warnings_ indicate potential problems, such as unused variable bindings.
 4. _Errors_ explain why parsing and elaboration could not complete.

By default, trace messages are hidden and the others are shown.
The threshold can be adjusted using the {lakeOpt}`--log-level` option, the {lakeOpt}`--verbose` flag, or the {lakeOpt}`--quiet` flag.
:::

## Builds

:::paragraph
Producing a desired {tech}[artifact], such as a {tech}[`.olean` file] or an executable binary, is called a {deftech}_build_.
Builds are triggered by the {lake}`build` command or by other commands that require an artifact to be present, such as {lake}`exe`.
A build consists of the following steps:

: {deftech key:="configure package"}[Configuring] the package

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
  Re-using prior build products when possible is called an {deftech}_incremental build_.

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

## Facets
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
  lake build [<targets>...]

A target is specified with a string of the form:

  [@[<package>]/][<target>|[+]<module>][:<facet>]

You can also use the source path of a module as a target. For example,

  lake build Foo/Bar.lean:o

will build the Lean module (within the workspace) whose source file is
`Foo/Bar.lean` and compile the generated C file into a native object file.

The `@` and `+` markers can be used to disambiguate packages and modules
from file paths or other kinds of targets (e.g., executables or libraries).

LIBRARY FACETS:         build the library's ...
  leanArts (default)    Lean artifacts (*.olean, *.ilean, *.c files)
  static                static artifact (*.a file)
  shared                shared artifact (*.so, *.dll, or *.dylib file)

MODULE FACETS:          build the module's ...
  deps                  dependencies (e.g., imports, shared libraries, etc.)
  leanArts (default)    Lean artifacts (*.olean, *.ilean, *.c files)
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

A bare `lake build` command will build the default target(s) of the root package.
Package dependencies are not updated during a build.
```


::::paragraph

The facets available for packages are:

```lean (show := false)
-- Always keep this in sync with the description below. It ensures that the list is complete.
/--
info: #[`package.barrel, `package.cache, `package.deps, `package.extraDep, `package.optBarrel, `package.optCache,
  `package.optRelease, `package.release, `package.transDeps]
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

```lean (show := false)
-- Always keep this in sync with the description below. It ensures that the list is complete.
/--
info: [`lean_lib.extraDep, `lean_lib.leanArts, `lean_lib.static.export, `lean_lib.shared, `lean_lib.modules, `lean_lib.static,
  `lean_lib.default]
-/
#guard_msgs in
#eval Lake.initLibraryFacetConfigs.toList.map (·.1)
```

:::paragraph

The facets available for libraries are:

: `leanArts`

  The artifacts that the Lean compiler produces for the library or executable ({tech key:=".olean files"}`*.olean`, `*.ilean`, and `*.c` files).

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

```lean (show := false)
-- Always keep this in sync with the description below. It ensures that the list is complete.
/--
info: module.bc
module.bc.o
module.c
module.c.o
module.c.o.export
module.c.o.noexport
module.deps
module.dynlib
module.header
module.ilean
module.imports
module.input
module.lean
module.leanArts
module.o
module.o.export
module.o.noexport
module.olean
module.olean.private
module.olean.server
module.precompileImports
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

: `leanArts` (default)

 The module's Lean artifacts (`*.olean`, `*.ilean`, `*.c` files).

: `deps`

  The module's dependencies (e.g., imports or shared libraries).

: `olean`

 The module's {tech}[`.olean` file]. {TODO}[Once module system lands fully, add docs for `olean.private` and `olean.server`]

: `ilean`

 The module's `.ilean` file, which is metadata used by the Lean language server.

: `header`

  The parsed module header of the module's source file.

: `imports`

  The immediate imports of the Lean module, but not the full set of transitive imports.

: `precompileImports`

  The transitive imports of the Lean module, compiled to object code.

: `transImports`

  The transitive imports of the Lean module, as {tech}[`.olean` files].

: `allImports`

  Both the immediate and transitive imports of the Lean module.

: `setup`

  All of a module's dependencies: transitive local imports and shared libraries to be loaded with `--load-dynlib`.
  Returns the list of shared libraries to load along with their search path.

: `c`

 The C file produced by the Lean compiler.

: `bc`

 LLVM bitcode file, produced by the Lean compiler.

: `c.o`

 The compiled object file, produced from the C file. On Windows, this is equivalent to `.c.o.noexport`, while it is equivalent to `.c.o.export` on other platforms.

: `c.o.export`

 The compiled object file, produced from the C file, with Lean symbols exported.

: `c.o.noexport`

 The compiled object file, produced from the C file, with Lean symbols exported.

: `bc.o`

 The compiled object file, produced from the LLVM bitcode file.

: `o`

 The compiled object file for the configured backend.

: `dynlib`

  A shared library (e.g., for the Lean option `--load-dynlib`){TODO}[Document Lean command line options, and cross-reference from here].

: `input`

  TODO

:::


## Scripts
%%%
tag := "lake-scripts"
%%%

Lake {tech}[package configuration] files may include {deftech}_Lake scripts_, which are embedded programs that can be executed from the command line.
Scripts are intended to be used for project-specific tasks that are not already well-served by Lake's other features.
While ordinary executable programs are run in the {name}`IO` {tech}[monad], scripts are run in {name Lake.ScriptM}`ScriptM`, which extends {name}`IO` with information about the workspace.
Because they are Lean definitions, Lake scripts can only be defined in the Lean configuration format.

:::::TODO

Restore the following once we can import enough of Lake to elaborate it

`````
```lean (show := false)
section
open Lake DSL
```

:::example "Listing Dependencies"

This Lake script lists all the transitive dependencies of the root package, along with their Git URLs, in alphabetical order.
Similar scripts could be used to check declared licenses, discover which dependencies have test drivers configured, or compute metrics about the transitive dependency set over time.

```lean
script "list-deps" := do
  let mut results := #[]
  for p in (← getWorkspace).packages do
    if p.name ≠ (← getWorkspace).root.name then
      results := results.push (p.name.toString, p.remoteUrl)
  results := results.qsort (·.1 < ·.1)
  IO.println "Dependencies:"
  for (name, url) in results do
    IO.println s!"{name}:\t{url}"
  return 0
```
:::

```lean (show := false)
end
```
`````

:::::

## Test and Lint Drivers
%%%
tag := "test-lint-drivers"
%%%

A {deftech}_test driver_ is responsible for running the tests for a package.
Test drivers may be executable targets or {tech}[Lake scripts], in which case the {lake}`test` command runs them, or they may be libraries, in which case {lake}`test` causes them to be elaborated, with the expectation that test failures are registered as elaboration failures.

Similarly, a {deftech}_lint driver_ is responsible for checking the code for stylistic issues.
Lint drivers may be executables or scripts, which are run by {lake}`lint`.

A test or lint driver can be configured by either setting the {tomlField Lake.PackageConfig}`testDriver` or {tomlField Lake.PackageConfig}`lintDriver` package configuration options or by tagging a script, executable, or library with the `test_driver` or `lint_driver` attribute in a Lean-format configuration file.
A definition in a dependency can be used as a test or lint driver by using the `<pkg>/<name>` syntax for the appropriate configuration option.
:::TODO
Restore the ``{attr}`` role for `test_driver` and `lint_driver` above. Right now, importing the attributes crashes the compiler.
:::

## GitHub Release Builds
%%%
tag := "lake-github"
%%%

Lake supports uploading and downloading build artifacts (i.e., the archived build directory) to/from the GitHub releases of packages.
This enables end users to fetch pre-built artifacts from the cloud without needed to rebuild the package from source themselves.
The {envVar}`LAKE_NO_CACHE` environment variable can be used to disable this feature.

### Downloading

To download artifacts, one should configure the package options `releaseRepo` and `buildArchive` to point to the GitHub repository hosting the release and the correct artifact name within it (if the defaults are not sufficient).
Then, set `preferReleaseBuild := true` to tell Lake to fetch and unpack it as an extra package dependency.

Lake will only fetch release builds as part of its standard build process if the package wanting it is a dependency (as the root package is expected to modified and thus not often compatible with this scheme).
However, should one wish to fetch a release for a root package (e.g., after cloning the release's source but before editing), one can manually do so via `lake build :release`.

Lake internally uses `curl` to download the release and `tar` to unpack it, so the end user must have both tools installed in order to use this feature.
If Lake fails to fetch a release for any reason, it will move on to building from the source.
This mechanism is not technically limited to GitHub: any Git host that uses the same URL scheme works as well.

### Uploading

To upload a built package as an artifact to a GitHub release, Lake provides the {lake}`upload` command as a convenient shorthand.
This command uses `tar` to pack the package's build directory into an archive and uses `gh release upload` to attach it to a pre-existing GitHub release for the specified tag.
Thus, in order to use it, the package uploader (but not the downloader) needs to have `gh`, the GitHub CLI, installed and in `PATH`.

{include 0 Manual.BuildTools.Lake.CLI}

{include 0 Manual.BuildTools.Lake.Config}

# Script API Reference
%%%
tag := "lake-api"
%%%

In addition to ordinary {lean}`IO` effects, Lake scripts have access to the Lake environment (which provides information about the current toolchain, such as the location of the Lean compiler) and the current workspace.
This access is provided in {name Lake.ScriptM}`ScriptM`.

{docstring Lake.ScriptM}

## Accessing the Environment

Monads that provide access to information about the current Lake environment (such as the locations of Lean, Lake, and other tools) have {name Lake.MonadLakeEnv}`MonadLakeEnv` instances.
This is true for all of the monads in the Lake API, including {name Lake.ScriptM}`ScriptM`.

{docstring Lake.MonadLakeEnv}

{docstring Lake.getLakeEnv}

{docstring Lake.getNoCache}

{docstring Lake.getTryCache}

{docstring Lake.getPkgUrlMap}

{docstring Lake.getElanToolchain}

### Search Path Helpers

{docstring Lake.getEnvLeanPath}

{docstring Lake.getEnvLeanSrcPath}

{docstring Lake.getEnvSharedLibPath}

### Elan Install Helpers

{docstring Lake.getElanInstall?}

{docstring Lake.getElanHome?}

{docstring Lake.getElan?}

### Lean Install Helpers

{docstring Lake.getLeanInstall}

{docstring Lake.getLeanSysroot}

{docstring Lake.getLeanSrcDir}

{docstring Lake.getLeanLibDir}

{docstring Lake.getLeanIncludeDir}

{docstring Lake.getLeanSystemLibDir}

{docstring Lake.getLean}

{docstring Lake.getLeanc}

{docstring Lake.getLeanSharedLib}

{docstring Lake.getLeanAr}

{docstring Lake.getLeanCc}

{docstring Lake.getLeanCc?}

### Lake Install Helpers

{docstring Lake.getLakeInstall}

{docstring Lake.getLakeHome}

{docstring Lake.getLakeSrcDir}

{docstring Lake.getLakeLibDir}

{docstring Lake.getLake}

## Accessing the Workspace

Monads that provide access to information about the current Lake workspace have {name Lake.MonadWorkspace}`MonadWorkspace` instances.
In particular, there are instances for {name Lake.ScriptM}`ScriptM` and {name Lake.LakeM}`LakeM`.

```lean (show := false)
section
open Lake
#synth MonadWorkspace ScriptM

end
```

{docstring Lake.MonadWorkspace}

{docstring Lake.getRootPackage}

{docstring Lake.findPackage?}

{docstring Lake.findModule?}

{docstring Lake.findLeanExe?}

{docstring Lake.findLeanLib?}

{docstring Lake.findExternLib?}

{docstring Lake.getLeanPath}

{docstring Lake.getLeanSrcPath}

{docstring Lake.getSharedLibPath}

{docstring Lake.getAugmentedLeanPath}

{docstring Lake.getAugmentedLeanSrcPath }

{docstring Lake.getAugmentedSharedLibPath}

{docstring Lake.getAugmentedEnv}
