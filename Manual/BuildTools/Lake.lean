/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Command
import Lake

import Manual.Meta
import Manual.BuildTools.Lake.CLI
import Manual.BuildTools.Lake.Config

open Manual
open Verso.Genre
open Verso.Genre.Manual


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
Packages contain {tech}[targets], such as libraries or executable programs, which are the basic unit of code to be built.
A package consist of a directory that contains a {tech}[package configuration] file together with source code.
Packages may {deftech}_require_ other packages, in which case those packages' code (more specifically, their {tech}[targets]) are made available.
The {deftech}_direct dependencies_ of a package are those that it requires, and the {deftech}_transitive dependencies_ are the direct dependencies of a package together with their transitive dependencies.
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

:::figure "Workspace Layout"
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

:::paragraph
A {deftech}_target_ represents a build product that can be requested by a user:

 * {deftech}_Libraries_ are collections of Lean {tech}[module]s, organized hierarchically under one or more {deftech}_module roots_.
 * {deftech}_Executables_ consist of a _single_ module that defines `main`
 * {deftech}_External libraries_ are non-Lean *static* libraries that will be linked to the binaries of the package and its dependents, including both their shared libraries and executables.
 * {deftech}_Custom targets_ contain arbitrary code to run a build, written using {name Lake.FetchM}`FetchM` in {TODO}[xref]Lake's API.
:::

:::TODO
Add static library targets after upcoming refactor
:::

An {deftech}_artifact_ is the persistent result of a build, such as object code, an executable binary, or an {tech}[`.olean` file].
Artifacts can result from builds at three levels of granularity: modules, targets, and packages.
There is a one-to-many relationship between each of these inputs and the resulting artifacts; for example, a building a module produces an `.olean` file and an `.ilean` file, along with a C source file that contains the code generated by Lean's compiler and an object file generated by the C compiler.

:::paragraph
The {deftech}_log_ contains information produced during a build.
Logs are saved so they can be replayed during {tech}[incremental builds].
Messages in the log have four levels, ordered by severity:

 1. _Trace messages_ contain internal build details that are often specific to the machine on which the build is running, including the specific invocations of Lean and other tools that are passed to the shell.
 2. _Informational messages_ contain general informational output that is not expected to indicate a problem with the code, such as the results of a {keywordOf Lean.Parser.Command.eval}`#eval` command.
 3. _Warnings_ indicate potential problems, such as unused variable bindings.
 4. _Errors_ explain why parsing and elaboration could not complete.
:::

## Builds

:::paragraph
Producing a desired {tech}[artifact], such as a {tech}[`.olean` file] or an executable binary, is called a {deftech}_build_.
Builds are triggered by the {lake}`build` command or by other commands that require an artifact to be present, such as {lake}`exe`.
A build consists of the following steps:

: Configuring the package

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
  During a build, Lake records which source files or other artifacts were used to produce each artifact, saving a hash of each input; these {deftech}_traces_ are saved in the {tech}[build directory].
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
This is a performance optimization.
If the modification time of the cached hash is later than that of the input file, then the cached hash is read.
This feature can be disabled, causing all hashes to be recomputed from scratch, using the `--rehash` command-line option.

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

A {deftech}_facet_ describes the production of an artifact from a module, target, or package.
Each kind of target has a default facet (e.g. producing an executable binary from an executable target); other facets may be specified explicitly in the {tech}[package configuration] or via Lake's {ref "lake-cli"}[command-line interface].
Lake's API may be used to write custom facets. {TODO}[xref]



```lakeHelp "build"
Build targets

USAGE:
  lake build [<targets>...]

A target is specified with a string of the form:

  [[@]<package>/][<target>|[+]<module>][:<facet>]

The optional `@` and `+` markers can be used to disambiguate packages
and modules from other kinds of targets (i.e., executables and libraries).

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
  a                     default facet of target `a`
  @a                    default target(s) of package `a`
  +A                    Lean artifacts of module `A`
  a/b                   default facet of target `b` of package `a`
  a/+A:c                C file of module `A` of package `a`
  :foo                  facet `foo` of the root package

A bare `lake build` command will build the default facet of the root package.
Package dependencies are not updated during a build.
```


::::paragraph

The facets available for packages are:

::: TODO

Confirm these with Mac

:::

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

:::paragraph

The facets available for targets (including libraries and executables) are:

: `leanArts`

  The artifacts that the Lean compiler produces for the library or executable ({tech key:=".olean files"}`*.olean`, `*.ilean`, and `*.c` files).

: `static`

  The static library produced by the C compiler from the `leanArts` (that is, a `*.a` file).

: `static.export`

  The static library produced by the C compiler from the `leanArts` (that is, a `*.a` file), with exported symbols.

: `shared`

  The shared library produced by the C compiler from the `leanArts` (that is, a `*.so`, `*.dll`, or `*.dylib` file, depending on the platform).

: `extraDep`

  A Lean library's {tomlField Lake.LeanLibConfig}`extraDepTargets` {TODO}[xref] and those of its package.

: `leanExe`

  The executable binary produced from a Lean executable target.
:::

:::paragraph
The facets available for modules are:

: `deps`


  The module's dependencies (e.g., imports or shared libraries).

: `leanArts` (default)

 The module's Lean artifacts (`*.olean`, `*.ilean`, `*.c` files)

: `olean`

 The module's {tech}[`.olean` file]

: `ilean`

 The module's `.ilean` file, which is metadata used by the Lean language server

: `c`

 The C file produced by the Lean compiler

: `bc`

 The compiled LLVM bitcode file produced from the Lean compiler's C file

: `c.o`

 The compiled object file, produced from the C file

: `bc.o`

 The compiled object file, produced from the LLVM bitcode file

: `o`

 The compiled object file for the configured backend

: `dynlib`

  A shared library (e.g., for the Lean option `--load-dynlib`){TODO}[document and xref Lean command line options]

:::


## Scripts
%%%
tag := "lake-scripts"
%%%

Lake {tech}[package configuration] files may include {deftech}_Lake scripts_, which are embedded programs that can be executed from the command line.
Scripts are intended to be used for project-specific tasks that are not already well-served by Lake's other features.
While ordinary executable programs are run in the {name}`IO` {tech}[monad], scripts are run in {name Lake.ScriptM}`ScriptM`, which extends {name}`IO` with information about the workspace.

Because they are Lean definitions, Lake scripts can only be defined in the Lean configuration format.

:::TODO
Example script, e.g. to enumerate and print all dependencies' licenses
:::

## Test and Lint Drivers
%%%
tag := "test-lint-drivers"
%%%

A {deftech}_test driver_ is responsible for running the tests for a package.
Test drivers may be executable targets or {tech}[Lake scripts], in which case the {lake}`test` command runs them, or they may be libraries, in which case {lake}`test` causes them to be elaborated, with the expectation that test failures are registered as elaboration failures.

Similarly, a {deftech}_lint driver_ is responsible for checking the code for stylistic issues.
Lint drivers may be executables or scripts, which are run by {lake}`lint`.

A test or lint driver can be configured by either setting the 'testDriver' or 'lintDriver' package configuration options or by tagging a script, executable, or library with the `@[test_driver]` or `@[lint_driver]` attribute in a Lean-format configuration file.
A definition in a dependency can be used as a test or lint driver by using the `<pkg>/<name>` syntax for the appropriate configuration option.

## GitHub Release Builds
%%%
tag := "lake-github"
%%%

:::TODO

Confirm with Mac: this is the same as a cached build from the perspective of `LAKE_NO_CACHE`, right?

:::

Lake supports uploading and downloading build artifacts (i.e., the archived build directory) to/from the GitHub releases of packages.
This enables end users to fetch pre-built artifacts from the cloud without needed to rebuild the package from source themselves.

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

# API Reference
%%%
tag := "lake-api"
%%%

{docstring Lake.FetchM}

{docstring Lake.FetchM.run}

{docstring Lake.RecBuildM}

{docstring Lake.RecBuildM.runJobM}

{docstring Lake.RecBuildM.run}

{docstring Lake.RecBuildM.run'}

{docstring Lake.ScriptM}

{docstring Lake.buildCycleError}

{docstring Lake.addLeanTrace}

{docstring Lake.addPlatformTrace}

{docstring Lake.addPureTrace}

{docstring Lake.addTrace}

{docstring Lake.binder}

{docstring Lake.binder.formatter}

{docstring Lake.binder.parenthesizer}

{docstring Lake.buildFileAfterDep}

{docstring Lake.buildFileUnlessUpToDate'}

{docstring Lake.buildImportsAndDeps}

{docstring Lake.buildLeanExe}

{docstring Lake.buildLeanO}

{docstring Lake.buildLeanSharedLib}

{docstring Lake.buildLeanSharedLibOfStatic}

{docstring Lake.buildO}

{docstring Lake.buildSpecs}

{docstring Lake.buildStaticLib}

{docstring Lake.buildUnlessUpToDate}

{docstring Lake.buildUnlessUpToDate?}

{docstring Lake.buildUnlessUpToDate?.go}

{docstring Lake.busyAcquireLockFile}

{docstring Lake.busyAcquireLockFile.busyLoop}

{docstring Lake.cacheFileHash}

{docstring Lake.captureProc}

{docstring Lake.captureProc?}

{docstring Lake.checkHashUpToDate}

{docstring Lake.clearFileHash}

{docstring Lake.collectImportsAux}

{docstring Lake.compileExe}

{docstring Lake.compileLeanModule}

{docstring Lake.compileO}

{docstring Lake.compileSharedLib}

{docstring Lake.compileStaticLib}

{docstring Lake.computeArrayHash}

{docstring Lake.computeArrayTrace}

{docstring Lake.computeBinFileHash}

{docstring Lake.computeDynlibOfShared}

{docstring Lake.computeFileHash}

{docstring Lake.computeHash}

{docstring Lake.computeListTrace}

{docstring Lake.computePrecompileImportsAux}

{docstring Lake.computeTextFileHash}

{docstring Lake.computeTrace}

{docstring Lake.createParentDirs}

{docstring Lake.customDataDecl}

{docstring Lake.declareOpaqueType}

{docstring Lake.defaultBinDir}

{docstring Lake.defaultBuildArchive}

{docstring Lake.defaultBuildDir}

{docstring Lake.defaultConfigFile}

{docstring Lake.defaultIrDir}

{docstring Lake.defaultLakeDir}

{docstring Lake.defaultLeanConfigFile}

{docstring Lake.defaultLeanLibDir}

{docstring Lake.defaultManifestFile}

{docstring Lake.defaultNativeLibDir}

{docstring Lake.defaultPackagesDir}

{docstring Lake.defaultScriptAttr}

{docstring Lake.defaultTargetAttr}

{docstring Lake.defaultTomlConfigFile}

{docstring Lake.defaultVersionTags}

{docstring Lake.dirExt}

{docstring Lake.doElemTry_Else_}

{docstring Lake.download}

{docstring Lake.drbmapOf}

{docstring Lake.dropLogFrom}

{docstring Lake.elabVerLit}

{docstring Lake.elabVerLit.unsafe_1}

{docstring Lake.elabVerLit.unsafe_impl_1}

{docstring Lake.ensureJob}

{docstring Lake.env}

{docstring Lake.envToBool?}

{docstring Lake.errorWithLog}

{docstring Lake.exe}

{docstring Lake.exitIfErrorCode}

{docstring Lake.expandBinderIdent}

{docstring Lake.expandBinderModifier}

{docstring Lake.expandBinderType}

{docstring Lake.expandBinders}

{docstring Lake.expandOptIdent}

{docstring Lake.expandOptType}

{docstring Lake.externLibAttr}

{docstring Lake.extractLog}

{docstring Lake.familyDef}

{docstring Lake.fetchFileHash}

{docstring Lake.fetchFileTrace}

{docstring Lake.fetchOrCreate}

{docstring Lake.findElanInstall?}

{docstring Lake.findExternLib?}

{docstring Lake.findInstall?}

{docstring Lake.findLakeInstall?}

{docstring Lake.findLakeLeanJointHome?}

{docstring Lake.findLeanCmdInstall?}

{docstring Lake.findLeanExe?}

{docstring Lake.findLeanInstall?}

{docstring Lake.findLeanLib?}

{docstring Lake.findLeanSysroot?}

{docstring Lake.findModule?}

{docstring Lake.findPackage?}

{docstring Lake.flush}

{docstring Lake.foldlUtf8}

{docstring Lake.foldlUtf8M}

{docstring Lake.getAugmentedEnv}

{docstring Lake.getAugmentedLeanPath}

{docstring Lake.getAugmentedLeanSrcPath}

{docstring Lake.getAugmentedSharedLibPath}

{docstring Lake.getBinderIds}

{docstring Lake.getBuildConfig}

{docstring Lake.getBuildContext}

{docstring Lake.getElan?}

{docstring Lake.getElanHome?}

{docstring Lake.getElanInstall?}

{docstring Lake.getElanToolchain}

{docstring Lake.getEnvLeanPath}

{docstring Lake.getEnvLeanSrcPath}

{docstring Lake.getEnvSharedLibPath}

{docstring Lake.getFileMTime}

{docstring Lake.getIsOldMode}

{docstring Lake.getIsQuiet}

{docstring Lake.getIsVerbose}

{docstring Lake.getLake}

{docstring Lake.getLakeEnv}

{docstring Lake.getLakeHome}

{docstring Lake.getLakeInstall}

{docstring Lake.getLakeInstall?}

{docstring Lake.getLakeLibDir}

{docstring Lake.getLakeSrcDir}

{docstring Lake.getLean}

{docstring Lake.getLeanAr}

{docstring Lake.getLeanCc}

{docstring Lake.getLeanCc?}

{docstring Lake.getLeanIncludeDir}

{docstring Lake.getLeanInstall}

{docstring Lake.getLeanLibDir}

{docstring Lake.getLeanPath}

{docstring Lake.getLeanSharedLib}

{docstring Lake.getLeanSrcDir}

{docstring Lake.getLeanSrcPath}

{docstring Lake.getLeanSysroot}

{docstring Lake.getLeanSystemLibDir}

{docstring Lake.getLeanTrace}

{docstring Lake.getLeanc}

{docstring Lake.getLog}

{docstring Lake.getLogPos}

{docstring Lake.getNoBuild}

{docstring Lake.getNoCache}

{docstring Lake.getPkgUrlMap}

{docstring Lake.getRootPackage}

{docstring Lake.getSearchPath}

{docstring Lake.getSharedLibPath}

{docstring Lake.getTrace}

{docstring Lake.getTrustHash}

{docstring Lake.getTryCache}

{docstring Lake.getUrl}

{docstring Lake.getVerbosity}

{docstring Lake.guardCycle}

{docstring Lake.hexEncodeByte}

{docstring Lake.hydrateOpaqueType}

{docstring Lake.initLibraryFacetConfigs}

{docstring Lake.initModuleFacetConfigs}

{docstring Lake.initPackageFacetConfigs}

{docstring Lake.initSharedLib}

{docstring Lake.inputBinFile}

{docstring Lake.inputFile}

{docstring Lake.inputTextFile}

{docstring Lake.instToJsonFilePath_lake}

{docstring Lake.isUriUnreservedMark}

{docstring Lake.isVerLike}

{docstring Lake.lakeBuildHome?}

{docstring Lake.lakeExe}

{docstring Lake.leanArExe}

{docstring Lake.leanCcExe}

{docstring Lake.leanExe}

{docstring Lake.leanExeAttr}

{docstring Lake.leanLibAttr}

{docstring Lake.leanSharedLib}

{docstring Lake.leanSharedLibDir}

{docstring Lake.leancExe}

{docstring Lake.libraryDataDecl}

{docstring Lake.libraryFacetAttr}

{docstring Lake.lintDriverAttr}

{docstring Lake.logError}

{docstring Lake.logInfo}

{docstring Lake.logOutput}

{docstring Lake.logSerialMessage}

{docstring Lake.logToStream}

{docstring Lake.logVerbose}

{docstring Lake.logWarning}

{docstring Lake.lpad}

{docstring Lake.matchBinder}

{docstring Lake.maybeRegisterJob}

{docstring Lake.mixTraceArray}

{docstring Lake.mixTraceList}

{docstring Lake.mkBuildContext}

{docstring Lake.mkBuildSpec}

{docstring Lake.mkCmdLog}

{docstring Lake.mkConfigBuildSpec}

{docstring Lake.mkDRBMap}

{docstring Lake.mkExceptionMessage}

{docstring Lake.mkFacetConfig}

{docstring Lake.mkFacetJobConfig}

{docstring Lake.mkHoleFrom}

{docstring Lake.mkLakeContext}

{docstring Lake.mkMessageLogString}

{docstring Lake.mkMessageNoPos}

{docstring Lake.mkMessageString}

{docstring Lake.mkMessageStringCore}

{docstring Lake.mkOrdNameMap}

{docstring Lake.mkParserErrorMessage}

{docstring Lake.mkRBArray}

{docstring Lake.mkRelPathString}

{docstring Lake.mkTargetFacetBuild}

{docstring Lake.mkTargetJobConfig}

{docstring Lake.moduleDataDecl}

{docstring Lake.moduleFacetAttr}

{docstring Lake.monitorJobs}

{docstring Lake.nameToSharedLib}

{docstring Lake.nameToStaticLib}

{docstring Lake.noBuildCode}

{docstring Lake.ofFamily}

{docstring Lake.optsExt}

{docstring Lake.packageAttr}

{docstring Lake.packageDataDecl}

{docstring Lake.packageDepAttr}

{docstring Lake.packageFacetAttr}

{docstring Lake.parseExeTargetSpec}

{docstring Lake.parsePackageSpec}

{docstring Lake.parseTargetSpec}

{docstring Lake.parseTargetSpecs}

{docstring Lake.platformTrace}

{docstring Lake.postUpdateAttr}

{docstring Lake.print!}

{docstring Lake.proc}

{docstring Lake.pureHash}

{docstring Lake.pushLogEntry}

{docstring Lake.rawProc}

{docstring Lake.readTraceFile?}

{docstring Lake.recBuildExternDynlibs}

{docstring Lake.recBuildWithIndex}

{docstring Lake.recFetch}

{docstring Lake.recFetchAcyclic}

{docstring Lake.recFetchMemoize}

{docstring Lake.registerJob}

{docstring Lake.registerOrderedTagAttribute}

{docstring Lake.resolveCustomTarget}

{docstring Lake.resolveDefaultPackageTarget}

{docstring Lake.resolveExeTarget}

{docstring Lake.resolveExternLibTarget}

{docstring Lake.resolveLibTarget}

{docstring Lake.resolveLibTarget.resolveFacet}

{docstring Lake.resolveModuleTarget}

{docstring Lake.resolvePackageTarget}

{docstring Lake.resolveTargetBaseSpec}

{docstring Lake.resolveTargetInPackage}

{docstring Lake.resolveTargetInWorkspace}

{docstring Lake.rpad}

{docstring Lake.runBuild}

{docstring Lake.scriptAttr}

{docstring Lake.setTrace}

{docstring Lake.sharedLibExt}

{docstring Lake.sharedLibPathEnvVar}

{docstring Lake.stringToLegalOrSimpleName}

{docstring Lake.takeLog}

{docstring Lake.takeLogFrom}

{docstring Lake.takeTrace}

{docstring Lake.tar}

{docstring Lake.targetAttr}

{docstring Lake.targetDataDecl}

{docstring Lake.termTry_Else_}

{docstring Lake.testDriverAttr}

{docstring Lake.testProc}

{docstring Lake.toFamily}

{docstring Lake.toUpperCamelCase}

{docstring Lake.toUpperCamelCaseString}

{docstring Lake.toolchainFileName}

{docstring Lake.uiVersionString}

{docstring Lake.untar}

{docstring Lake.updateAction}

{docstring Lake.uriEncode}

{docstring Lake.uriEncodeChar}

{docstring Lake.uriEscapeByte}

{docstring Lake.uriEscapeChar}

{docstring Lake.verLit}

{docstring Lake.version.isRelease}

{docstring Lake.version.major}

{docstring Lake.version.minor}

{docstring Lake.version.patch}

{docstring Lake.version.specialDesc}

{docstring Lake.versionString}

{docstring Lake.versionStringCore}

{docstring Lake.versionTagPresets}

{docstring Lake.withExtractLog}

{docstring Lake.withLockFile}

{docstring Lake.withLogErrorPos}

{docstring Lake.withLoggedIO}

{docstring Lake.withRegisterJob}

{docstring Lake.writeTraceFile}

{docstring Lake.zpad}
