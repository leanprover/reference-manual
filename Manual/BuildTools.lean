/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Command

import Manual.Meta

open Manual
open Verso.Genre
open Verso.Genre.Manual


open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode


#doc (Manual) "Lake and Reservoir" =>
%%%
tag := "build-tools-and-distribution"
%%%

# Lake
%%%
tag := "lake"
%%%

::: planned 75
 * Port and organize the information in the Lake README
 * Describe the underlying Lake-specific concepts of traces, artifacts, workspaces, and facets
:::


Lake is the standard Lean build tool.
It is responsible for packages, which are the unit of code distribution.
Packages may contain multiple libraries and/or executables - these are targets.

UI Concepts

When I build a target, the packages' dependencies are built before the target.

Two notions of dependencies:
 * Packages depend on packages
 * Targets may depend on targets from other package
 * "ExtraDepTargets" imposes dependencies on all targets in a package

A target is something I wish to ask for - the user requests it. Front-facing name of the thing I want to ask for.
A build product on disk is named by a target and a facet. Each target has a default facet.

A build product is an _artifact_ - any persistent result.

The "workspace" is also part of the UI

A workspace is the full set of all required packages.
The "known universe" to lake.
Relevant when setting up the server - the server needs to know all the code to point at.
The workspace is composed of multiple packages - incl. the root package.
The root package is the one whose config file is read.

Package is unit of distribution, workspace is the name of the local files.

What is query? It's a way to get output from Lake from a target that doesn't go through a target.
Mostly machine-readable, and not interleaved with all the log stuff.

Pack/unpack: related to cloud releases/cloud build archives.
They give a "crate"/"uncrate".
They "zip up the build dir" essentially - unless platform independent option is set (no platform traces)
These are beta features

Upload: perhaps use from GH action?

It's an error if there's an incomplete manifest

Configuring a package is to parse the configuration, apply the options.
This is a one-time thing, and you must use `-R`.
Configuration happens again if the file changes, but changes to -K options require -R

Log levels: "trace" is hidden unless verbose

Modules in Lake are Lean modules + potentially generated ones not existing as code in the users's source directory
Module is the unit of code visible to the build system (smallest code unit visible to the build system)

Targets are:
 * Libraries - collection of Lean modules
 * Exes - a single module that has `main` in it
 * External libs - add as a TODO due to upcoming refactor
 * Static library - likewise
 * Custom targets - Any arbitrary set of build code. Operates in different monads from scripts (FetchM vs ScriptM). Targets produce jobs. Custom targets don't have facets.

Test driver: exe, script, library

Linters: exe or script

The check- versions are used to tell whether the problem is failing tests/lints vs misconfigured builds

:::TODO

What does Lake do and what does it not do?

Manifests

:::



## Command-Line Interface


```lakeHelp
USAGE:
  lake [OPTIONS] <COMMAND>

COMMANDS:
  new <name> <temp>     create a Lean package in a new directory
  init <name> <temp>    create a Lean package in the current directory
  build <targets>...    build targets
  exe <exe> <args>...   build an exe and run it in Lake's environment
  check-build           check if any default build targets are configured
  test                  test the package using the configured test driver
  check-test            check if there is a properly configured test driver
  lint                  lint the package using the configured lint driver
  check-lint            check if there is a properly configured lint driver
  clean                 remove build outputs
  env <cmd> <args>...   execute a command in Lake's environment
  lean <file>           elaborate a Lean file in Lake's context
  update                update dependencies and save them to the manifest
  pack                  pack build artifacts into an archive for distribution
  unpack                unpack build artifacts from an distributed archive
  upload <tag>          upload build artifacts to a GitHub release
  script                manage and run workspace scripts
  scripts               shorthand for `lake script list`
  run <script>          shorthand for `lake script run`
  translate-config      change language of the package configuration
  serve                 start the Lean language server

BASIC OPTIONS:
  --version             print version and exit
  --help, -h            print help of the program or a command and exit
  --dir, -d=file        use the package configuration in a specific directory
  --file, -f=file       use a specific file for the package configuration
  -K key[=value]        set the configuration file option named key
  --old                 only rebuild modified modules (ignore transitive deps)
  --rehash, -H          hash all files for traces (do not trust `.hash` files)
  --update, -U          update dependencies on load (e.g., before a build)
  --packages=file       JSON file of package entries that override the manifest
  --reconfigure, -R     elaborate configuration files instead of using OLeans
  --keep-toolchain      do not update toolchain on workspace update
  --no-build            exit immediately if a build target is not up-to-date
  --no-cache            build packages locally; do not download build caches
  --try-cache           attempt to download build caches for supported packages

OUTPUT OPTIONS:
  --quiet, -q           hide informational logs and the progress indicator
  --verbose, -v         show trace logs (command invocations) and built targets
  --ansi, --no-ansi     toggle the use of ANSI escape codes to prettify output
  --log-level=lv        minimum log level to output on success
                        (levels: trace, info, warning, error)
  --fail-level=lv       minimum log level to fail a build (default: error)
  --iofail              fail build if any I/O or other info is logged
                        (same as --fail-level=info)
  --wfail               fail build if warnings are logged
                        (same as --fail-level=warning)


See `lake help <command>` for more information on a specific command.
```

Lake's command-line interface provides a number of global options as well as subcommands that perform important tasks.

### Creating Packages

:::TODO

`lake init` and `lake new`

:::

### Building and Running

:::TODO

`lake build` and `lake exe` and `lake clean` and `lake env` and `lake lean`

:::

### Development Tools

:::TODO

`lake test` and `lake lint`

`lake check-test` and `lake check-lint`

`lake script`

`lake scripts`

`lake run`

`lake serve`

:::

### Dependency Management

:::TODO

`lake update`

:::


### Configuration Files

:::TODO

`lake translate-config`

:::


## Configuration File Format

## API Reference
%%%
tag := "lake-api"
%%%

# Reservoir
%%%
tag := "reservoir"
%%%


::: planned 76
 * Concepts
 * Package and toolchain versions
 * Tags and builds
:::
