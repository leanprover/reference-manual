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
import Manual.BuildTools.Lake.API
import Manual.BuildTools.Lake.Builds
import Manual.BuildTools.Lake.Cache
import Manual.BuildTools.Lake.CLI
import Manual.BuildTools.Lake.Config
import Manual.BuildTools.Lake.Drivers
import Manual.BuildTools.Lake.PackageOverrides
import Manual.BuildTools.Lake.Scripts

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
 * Configuring {tech}[builds] and building Lean code
 * Fetching and building external {tech}[dependencies]
 * Integrating with [Reservoir](https://reservoir.lean-lang.org/){TODO}[xref chapter], the Lean package server
 * Running tests, linters, and other {tech}[development workflows]

Lake is extensible.
It provides a rich API that can be used to define incremental build tasks for software artifacts that are not written in Lean, to automate administrative tasks, and to integrate with external workflows.
For build configurations that do not need these features, Lake provides a declarative configuration language that can be written either in TOML or as a Lean file.

This section describes Lake's {ref "lake-builds"}[builds], {ref "lake-cache"}[cache], {ref "lake-workflows"}[workflows], {ref "lake-cli"}[command-line interface], {ref "lake-config"}[configuration files], and {ref "lake-api"}[internal API].
They all share a set of concepts and terminology.


# Concepts and Terminology
%%%
tag := "lake-vocab"
%%%

A {deftech}_package_ is the basic unit of Lean code distribution.
A single package may contain multiple libraries or executable programs.
A package consist of a directory that contains a {tech}[package configuration] file together with source code.
Packages may {deftech}_require_ other packages as {deftech}_dependencies_, in which case those packages' code (more specifically, their {tech}[targets]) are made available.
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

 * `lean-toolchain`: The {tech}[toolchain file].
 * `lakefile.toml` or `lakefile.lean`: The {tech}[package configuration] file for the root package.
 * `lake-manifest.json`: The root package's {tech}[manifest].
 * `.lake/`: Intermediate state managed by Lake, such as built {tech}[artifacts] and dependency source code.
   * `.lake/lakefile.olean`: The root package's configuration, cached.
   * `.lake/packages/`: The workspace's {deftech}_package directory_, which contains copies of all non-local transitive dependencies of the root package, with their built artifacts in their own `.lake` directories.
   * `.lake/build/`: The {deftech}_build directory_, which contains built artifacts for the root package:
     * `.lake/build/bin`: The package's {deftech}_binary directory_, which contains built executables.
     * `.lake/build/lib`: The package's _library directory_, which contains built libraries and {tech}[`.olean` files].
     * `.lake/build/ir`: The package's intermediate result directory, which contains generated intermediate artifacts, primarily C code.
:::

:::figure "Workspace Layout" (tag :="workspace-layout")
```diagram
open Illuminate in
  let txt (s : String) (size : Float := 10) : Diagram SVG :=
    .text s { fontSize := size, anchor := TextAnchor.start }
  let bold (s : String) (size : Float := 11) : Diagram SVG :=
    .text s { fontSize := size, bold := true, anchor := TextAnchor.start }
  let mono (s : String) (size : Float := 10) : Diagram SVG :=
    .text s { fontSize := size, fontFamily := "monospace", anchor := TextAnchor.start }
  let items (ss : List String) (size : Float := 10) : Diagram SVG :=
    Diagram.vsep 3 (ss.map fun s => txt s size) (align := .left)
  let borderedBox (title : String) (content : Diagram SVG)
      (titleSize : Float := 11) (pad : Float := 8) : Diagram SVG :=
    Diagram.vsep 4 [bold title titleSize, content] (align := .left)
      |>.pad pad |>.frame (padding := 2) (cornerRadius := 4)

  let toolchain := mono "lean-toolchain"
  let rootPkg := borderedBox "Root package" <|
    items [
      "Package configuration file (lakefile.lean)",
      "Libraries",
      "Executables",
      "Manifest (lake-manifest.json)"
    ]
  let depItems := items ["Package configuration file", "Libraries", "Executables", "Artifacts"] 8
  let dep1 := borderedBox "Dependency 1" depItems 9 6
  let dep2 := borderedBox "Dependency 2" depItems 9 6
  let dots : Diagram SVG := .text "⋯" { fontSize := 14 }
  let packages := borderedBox "Packages" <|
    Diagram.vsep 8 [Diagram.hsep 12 [dep1, dep2], dots] (align := .left)
  let artifacts := borderedBox "Artifacts" <|
    items ["Built libraries", "Built executables"]
  let lakeDir := borderedBox "Lake Directory (.lake)" <|
    Diagram.vsep 10 [packages, artifacts] (align := .left)
  borderedBox "Workspace" <|
    Diagram.vsep 10 [toolchain, rootPkg, lakeDir] (align := .left)


```
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

{include 2 Manual.BuildTools.Lake.PackageOverrides}

{include 0 Manual.BuildTools.Lake.Builds}

{include 0 Manual.BuildTools.Lake.Cache}

# Development Workflows
%%%
tag := "lake-workflows"
%%%

Lake provides tools to execute standard {deftech}_development workflows_ for a package through its own CLI.
For the common cases of testing and linting, Lake provides builtin support through the {lake}`test` and {lake}`lint` commands, which use the {ref "test-lint-drivers"}[test and lint drivers] configured on the package.
For other workflows, Lake provides {ref "lake-scripts"}[scripts], custom programs with ready access to the {ref "lake-api"}[Lake API], defined in the Lean configuration format and run through the {lake}`scripts` CLI.

{include 2 Manual.BuildTools.Lake.Drivers}

{include 2 Manual.BuildTools.Lake.Scripts}

{include 0 Manual.BuildTools.Lake.CLI}

{include 0 Manual.BuildTools.Lake.Config}

{include 0 Manual.BuildTools.Lake.API}
