/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Command
import Lake

import Manual.Meta

open Manual
open Verso.Genre
open Verso.Genre.Manual


open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "Command-Line Interface" =>
%%%
tag := "lake-cli"
%%%


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

Lake's command-line interface is structured into a series of subcommands.
All of the subcommands share a the ability to be configured by certain environment variables and global command-line options.
Each subcommand should be understood as a utility in its own right, with its own required argument syntax and documentation.

:::paragraph
Some of Lake's commands delegate to other command-line utilities that are not included in a Lean distribution.
These utilities must be available on the `PATH` in order to use the corresponding features:

 * `git` is required in order to access Git dependencies.
 * `tar` is required to create or extract cloud build archives, and `curl` is required to fetch them.
 * `gh` is required to upload build artifacts to GitHub releases.

Lean distributions include a C compiler toolchain.
:::

# Environment Variables
%%%
tag := "lake-environment"
%%%

```lakeHelp "env"
Execute a command in Lake's environment

USAGE:
  lake env [<cmd>] [<args>...]

Spawns a new process executing `cmd` with the given `args` and with
the environment set based on the detected Lean/Lake installations and
the workspace configuration (if it exists).

Specifically, this command sets the following environment variables:

  LAKE                  set to the detected Lake executable
  LAKE_HOME             set to the detected Lake home
  LEAN_SYSROOT          set to the detected Lean toolchain directory
  LEAN_AR               set to the detected Lean `ar` binary
  LEAN_CC               set to the detected `cc` (if not using the bundled one)
  LEAN_PATH             adds Lake's and the workspace's Lean library dirs
  LEAN_SRC_PATH         adds Lake's and the workspace's source dirs
  PATH                  adds Lean's, Lake's, and the workspace's binary dirs
  PATH                  adds Lean's and the workspace's library dirs (Windows)
  DYLD_LIBRARY_PATH     adds Lean's and the workspace's library dirs (MacOS)
  LD_LIBRARY_PATH       adds Lean's and the workspace's library dirs (other)

A bare `lake env` will print out the variables set and their values,
using the form NAME=VALUE like the POSIX `env` command.
```


When invoking the Lean compiler or other tools, Lake sets or modifies a number of environment variables.{index}[environment variables]
These values are system-dependent.
Invoking {lake}`env` without any arguments displays the environment variables and their values.
Otherwise, {lakeMeta}`cmd` is invoked in Lake's environment with arguments {lakeMeta}`args`.

::::paragraph
The following variables are set, overriding previous values:
:::table align:=left
* row
  * {envVar def:=true}`LAKE`
  * The detected Lake executable
* row
  * {envVar}`LAKE_HOME`
  * The detected {tech}[Lake home]
* row
  * {envVar}`LEAN_SYSROOT`
  * The detected Lean {tech}[toolchain] directory
* row
 * {envVar}`LEAN_AR`
 * The detected Lean `ar` binary
* row
  * {envVar}`LEAN_CC`
  * The detected C compiler (if not using the bundled one)
:::
::::

::::paragraph
The following variables are augmented with additional information:
:::table align:=left
* row
  * {envVar}`LEAN_PATH`
  * Lake's and the {tech}[workspace]'s Lean {tech}[library directories] are added.
* row
  * {envVar}`LEAN_SRC_PATH`
  * Lake's and the {tech}[workspace]'s {tech}[source directories] are added.
* row
  * {envVar}`PATH`
  * Lean's, Lake's, and the {tech}[workspace]'s {tech}[binary directories] are added.
    On Windows, Lean's and the {tech}[workspace]'s {tech}[library directories] are also added.
* row
  * {envVar}`DYLD_LIBRARY_PATH`
  * On macOS, Lean's and the {tech}[workspace]'s {tech}[library directories] are added.
* row
  * {envVar}`LD_LIBRARY_PATH`
  * On platforms other than Windows and macOS, Lean's and the {tech}[workspace]'s {tech}[library directories] are added.
:::
::::

::::paragraph
Lake itself can be configured with the following environment variables:
:::table align:=left
* row
  * {envVar def:=true}`ELAN_HOME`
  * The location of the {ref "elan"}[Elan] installation, which is used for {ref "automatic-toolchain-updates"}[automatic toolchain updates].
    The {envVar def:=true}`ELAN` variable, pointing at the `elan` binary, is used as a fallback, followed by an occurrence of `elan` found on the {envVar}`PATH`.
* row
  * {envVar def:=true}`LAKE_HOME`
  * The location of the Lake installation.
    This environment variable is only consulted when Lake is unable to determine its installation path from the location of the `lake` executable that's currently running.
* row
  * {envVar def:=true}`LEAN_SYSROOT`
  * The location of the Lean installation, used to find the Lean compiler, the standard library, and other bundled tools.
    Lake first checks whether its binary is colocated with a Lean install, using that installation if so.
    If not, or if {envVar def:=true}`LAKE_OVERRIDE_LEAN` is true, then Lake consults {envVar}`LEAN_SYSROOT`.
    If this is not set, Lake consults the {envVar def:=true}`LEAN` environment variable to find the Lean compiler, and attempts to find the Lean installation relative to the compiler.
    If {envVar}`LEAN` is set but empty, Lake considers Lean to be disabled.
    If {envVar}`LEAN_SYSROOT` and {envVar}`LEAN` are unset, the first occurrence of `lean` on the {envVar}`PATH` is used to find the installation.
* row
  * {envVar def:=true}`LEAN_CC` and {envVar def:=true}`LEAN_AR`
  * If {envVar}`LEAN_CC` and/or {envVar}`LEAN_AR` is set, its value is used as the C compiler or `ar` command when building libraries.
    If not, Lake will fall back to the bundled tool in the Lean installation.
    If the bundled tool is not found, the value of {envVar def:=true}`CC` or {envVar def:=true}`AR`, followed by a `cc` or `ar` on the {envVar}`PATH`, are used.
* row
  * {envVar def:=true}`LAKE_NO_CACHE`
  * If true, Lake does not use cached builds from {ref "reservoir"}[Reservoir] or {ref "lake-github"}[GitHub].
    This environment variable can be overridden using the {lakeOpt}`--try-cache` command-line option.

:::
::::

Lake considers an environment variable to be true when its value is `y`, `yes`, `t`, `true`, `on`, or `1`, compared case-insensitively.
It considers a variable to be false when its value is `n`, `no`, `f`, `false`, `off`, or `0`, compared case-insensitively.
If the variable is unset, or its value is neither true nor false, a default value is used.

```lean (show := false)
-- Test the claim above
/--
info: def Lake.envToBool? : String → Option Bool :=
fun o =>
  if ["y", "yes", "t", "true", "on", "1"].contains o.toLower = true then some true
  else if ["n", "no", "f", "false", "off", "0"].contains o.toLower = true then some false else none
-/
#guard_msgs in
#print Lake.envToBool?
```

# Options

Lake's command-line interface provides a number of global options as well as subcommands that perform important tasks.
Single-character flags cannot be combined; `-HU` is not equivalent to `-H -U`.

: {lakeOptDef flag}`--version`

  Lake outputs its version and exits without doing anything else.

: {lakeOptDef flag}`--help` or {lakeOptDef flag}`-h`

  Lake outputs its version and exits without doing anything else.

: {lakeOptDef option}`--dir DIR` or {lakeOptDef option}`-d=DIR`

  Use the provided directory as location of the package instead of the current working directory.
  This is not always equivalent to changing to the directory first, because the version of `lake` indicated by the current directory's {tech}[toolchain file] will be used, rather than that of `DIR`.

: {lakeOptDef option}`--file FILE` or {lakeOptDef option}`-f=FILE`

  Use the specified {tech}[package configuration] file instead of the default.

: {lakeOptDef flag}`--old`

  Only rebuild modified modules, ignoring transitive dependencies.
  Modules that import the modified module will not be rebuilt.
  In order to accomplish this, file modification times are used instead of hashes to determine whether a module has changed.

: {lakeOptDef flag}`--rehash` or {lakeOptDef flag}`-H`

  Ignored cached file hashes, recomputing them.
  Lake uses hashes of dependencies to determine whether to rebuild an artifact.
  These hashes are cached on disk whenever a module is built.
  To save time during builds, these cached hashes are used instead of recomputing each hash unless {lakeOpt}`--rehash` is specified.


: {lakeOptDef flag}`--update` or {lakeOptDef flag}`-U`

  Update dependencies after the {tech}[package configuration] is loaded but prior to performing other tasks, such as a build.
  This is equivalent to running `lake update` before the selected command, but it may be faster due to not having to load the configuration twice.

: {lakeOptDef option}`--packages=FILE`

  Use the contents of `FILE` to specify the versions of each dependency instead of the manifest.
  `FILE` should be a valid manifest.

:  {lakeOptDef flag}`--reconfigure` or {lakeOptDef flag}`-R`

  Normally, the {tech}[package configuration] file is {tech key:="elaborator"}[elaborated] when a package is first configured, with the result cached to a {tech}[`.olean` file] that is used for future invocations until the package configuration
  Providing this flag causes the configuration file to be re-elaborated.

: {lakeOptDef flag}`--keep-toolchain`

  By default, Lake attempts to update the local {tech}[workspace]'s {tech}[toolchain file].
  Providing this flag disables {ref "automatic-toolchain-updates"}[automatic toolchain updates].

: {lakeOptDef flag}`--no-build`

  Lake exits immediately if a build target is not up-to-date, returning a non-zero exit code.

: {lakeOptDef flag}`--no-cache`

  Instead of using available cloud build caches, build all packages locally.
  Build caches are not downloaded.

: {lakeOptDef flag}`--try-cache`

  attempt to download build caches for supported packages

# Controlling Output

These options provide allow control over the {tech}[log] that is produced while building.
In addition to showing or hiding messages, a build can be made to fail when warnings or even information is emitted; this can be used to enforce a style guide that disallows output during builds.

: {lakeOptDef flag}`--quiet`, {lakeOptDef flag}`-q`

  Hides informational logs and the progress indicator.

: {lakeOptDef flag}`--verbose`, {lakeOptDef flag}`-v`

  Shows trace logs (typically command invocations) and built {tech}[targets].

:  {lakeOptDef flag}`--ansi`, {lakeOptDef flag}`--no-ansi`

  Enables or disables the use of [ANSI escape codes](https://en.wikipedia.org/wiki/ANSI_escape_code) that add colors and animations to Lake's output.

:  {lakeOptDef option}`--log-level=LV`

  Sets the minimum level of {tech}[logs] to be shown when builds succeed.
  `LV` may be `trace`, `info`, `warning`, or `error`, compared case-insensitively.
  When a build fails, all levels are shown.
  The default log level is `info`.

:  {lakeOptDef option}`--fail-level=LV`

  Sets the threshold at which a message in the {tech}[log] causes a build to be considered a failure.
  If a message is emitted to the log with a level that is greater than or equal to the threshold, the build fails.
  `LV` may be `trace`, `info`, `warning`, or `error`, compared case-insensitively; it is `error` by default.


: {lakeOptDef flag}`--iofail`

  Causes builds to fail if any I/O or other info is logged.
  This is equivalent to {lakeOpt}`--fail-level=info`.

: {lakeOptDef flag}`--wfail`

  Causes builds to fail if any warnings are logged.
  This is equivalent to {lakeOpt}`--fail-level=warning`.

# Automatic Toolchain Updates
%%%
tag := "automatic-toolchain-updates"
%%%

The {lake}`update` command checks for changes to dependencies, fetching their sources and updating the {tech}[manifest] accordingly.
By default, {lake}`update` also attempts to update the {tech}[root package]'s {tech}[toolchain file] when a new version of a dependency specifies an updated toolchain.
This behavior can be disabled with the {lakeOpt}`--keep-toolchain` flag.

:::paragraph
If multiple dependencies specify newer toolchains, Lake selects the newest compatible toolchain, if it exists.
To determine the newest compatible toolchain, Lake parses the toolchain listed in the packages' `lean-toolchain` files into four categories:

 * Releases, which are compared by version number (e.g., `v4.4.0` < `v4.8.0` and `v4.6.0-rc1` < `v4.6.0`)
 * Nightly builds, which are compared by date (e.g., `nightly-2024-01-10` < `nightly-2024-10-01`)
 * Builds from pull reqeusts to the Lean compiler, which are incomparable
 * Other versions, which are also incomparable

Toolchain versions from multiple categories are incomparable.
If there is not a single newest toolchain, Lake will print a warning and continue updating without changing the toolchain.
:::

If Lake does find a new toolchain, then it updates the {tech}[workspace]'s `lean-toolchain` file accordingly and restarts the {lake}`update` using the new toolchain's Lake.
If {ref "elan"}[Elan] is detected, it will spawn the new Lake process via `elan run` with the same arguments Lake was initially run with.
If Elan is missing, it will prompt the user to restart Lake manually and exit with a special error code (namely, `4`).
The Elan executable used by Lake can be configured using the {envVar}`ELAN` environment variable.


# Creating Packages

```lakeHelp "new"
Create a Lean package in a new directory

USAGE:
  lake new <name> [<template>][.<language>]

The initial configuration and starter files are based on the template:

  std                   library and executable; default
  exe                   executable only
  lib                   library only
  math                  library only with a mathlib dependency

Templates can be suffixed with `.lean` or `.toml` to produce a Lean or TOML
version of the configuration file, respectively. The default is Lean.
```

:::lake new "name [template][\".\"language]"

Running {lake}`new` creates an initial Lean package in a new directory.
This command is equivalent to creating a directory named {lakeMeta}`name` and then running {lake}`init`

:::

:::lake init "name [template][\".\"language]"

Running {lake}`init` creates an initial Lean package in the current directory.
The package's contents are based on a template, with the names of the {tech}[package], its {tech}[targets], and their {tech}[module roots] derived from the name of the current directory.

The {lakeMeta}`template` may be:

: `std` (default)

  Creates a package that contains a library and an executable.

: `exe`

  Creates a package that contains only an executable.

: `lib`

  Creates a package that contains only a library.

: `math`

  Creates a package that contains a library that depends on [Mathlib](https://github.com/leanprover-community/mathlib4).

The {lakeMeta}`language` selects the file format used for the {tech}[package configuration] file and may be `lean` (the default) or `toml`.
:::

:::TODO
Example of `lake init` or `lake new`
:::

# Building and Running

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

:::lake build "[targets...]"

Builds the specified facts of the specified targets.

Each of the {lakeMeta}`targets` is specified by a string of the form:

{lakeArgs}`[["@"]package"/"][target|["+"]module][":"facet]`

The optional {keyword}`@` and {keyword}`+` markers can be used to disambiguate packages and modules from executables and libraries.
If not provided, {lakeMeta}`package` defaults to the {tech}[workspace]'s {tech}[root package].
If the same target name exists in multiple packages in the workspace, then the first occurrence of the target name found in a topological sort of the package dependency graph is selected.

The available {tech}[facets] depend on whether a package, target, or module is to be built.
They are listed in {ref "lake-facets"}[the section on facets].

:::

::::example "Target and Facet Specifications"

:::table
* ignored
  - `a`
  - The {tech}[default facet] of target `a`
* ignored
  - `@a`
  - The {tech}[default targets] of {tech}[package] `a`
* ignored
  - `+A`
  -  The Lean artifacts of module `A` (because the default facet of modules is `leanArts`)
* ignored
  - `a/b`
  - The default facet of target `b` of package `a`
* ignored
  - `a/+A:c`
  - The C file compiled from module `A` of package `a`
* ignored
  - `:foo`
  - The {tech}[root package]'s facet `foo`
:::
::::

```lakeHelp "exe"
Build an executable target and run it in Lake's environment

USAGE:
  lake exe <exe-target> [<args>...]

ALIAS: lake exec

Looks for the executable target in the workspace (see `lake help build` to
learn how to specify targets), builds it if it is out of date, and then runs
it with the given `args` in Lake's environment (see `lake help env` for how
the environment is set up).
```

:::lake exe "«exe-target» [args...]" (alias := exec)

Looks for the executable target {lakeMeta}`exe-target` in the workspace, builds it if it is out of date, and then runs
it with the given {lakeMeta}`args` in Lake's environment.

See {lake}`build` for the syntax of target specifications and {lake}`env` for a description of how the environment is set up.

:::

```lakeHelp "clean"
Remove build outputs

USAGE:
  lake clean [<package>...]

If no package is specified, deletes the build directories of every package in
the workspace. Otherwise, just deletes those of the specified packages.
```

:::lake clean "[packages...]"

If no package is specified, deletes the {tech}[build directories] of every package in the workspace.
Otherwise, it just deletes those of the specified {lakeMeta}`packages`.

:::

```lakeHelp "env"
Execute a command in Lake's environment

USAGE:
  lake env [<cmd>] [<args>...]

Spawns a new process executing `cmd` with the given `args` and with
the environment set based on the detected Lean/Lake installations and
the workspace configuration (if it exists).

Specifically, this command sets the following environment variables:

  LAKE                  set to the detected Lake executable
  LAKE_HOME             set to the detected Lake home
  LEAN_SYSROOT          set to the detected Lean toolchain directory
  LEAN_AR               set to the detected Lean `ar` binary
  LEAN_CC               set to the detected `cc` (if not using the bundled one)
  LEAN_PATH             adds Lake's and the workspace's Lean library dirs
  LEAN_SRC_PATH         adds Lake's and the workspace's source dirs
  PATH                  adds Lean's, Lake's, and the workspace's binary dirs
  PATH                  adds Lean's and the workspace's library dirs (Windows)
  DYLD_LIBRARY_PATH     adds Lean's and the workspace's library dirs (MacOS)
  LD_LIBRARY_PATH       adds Lean's and the workspace's library dirs (other)

A bare `lake env` will print out the variables set and their values,
using the form NAME=VALUE like the POSIX `env` command.
```

::::lake env "[cmd [args...]]"

When {lakeMeta}`cmd` is provided, it is executed in {ref "lake-environment"}[the Lake environment] with arguments {lakeMeta}`args`.

If {lakeMeta}`cmd` is not provided, Lake prints the environment in which it runs tools.
This environment is system-specific.
::::

```lakeHelp "lean"
Elaborate a Lean file in the context of the Lake workspace

USAGE:
  lake lean <file> [-- <args>...]

Build the imports of the given file and then runs `lean` on it using
the workspace's root package's additional Lean arguments and the given args
(in that order). The `lean` process is executed in Lake's environment like
`lake env lean` (see `lake help env` for how the environment is set up).
```

:::lake lean "file [\"--\" args...]"

Builds the imports of the given {lakeMeta}`file` and then runs `lean` on it using the {tech}[workspace]'s {tech}[root package]'s additional Lean arguments and the given {lakeMeta}`args`, in that order.
The `lean` process is executed in {ref "lake-environment"}[Lake's environment].
:::


# Development Tools

Lake includes support for specifying standard development tools and workflows.
On the command line, these tools can be invoked using the appropriate `lake` subcommands.

## Tests and Linters

```lakeHelp test
Test the workspace's root package using its configured test driver

USAGE:
  lake test [-- <args>...]

A test driver can be configured by either setting the 'testDriver'
package configuration option or by tagging a script, executable, or library
`@[test_driver]`. A definition in a dependency can be used as a test driver
by using the `<pkg>/<name>` syntax for the 'testDriver' configuration option.

A script test driver will be run with the  package configuration's
`testDriverArgs` plus the CLI `args`. An executable test driver will be
built and then run like a script. A library test driver will just be built.

```

:::lake test " [\"--\" args...]"
Test the workspace's root package using its configured {tech}[test driver].

A test driver that is an executable will be built and then run with the package configuration's `testDriverArgs` plus the CLI {lakeMeta}`args`.
A test driver that is a {tech}[Lake script] is run with the same arguments as an executable test driver.
A library test driver will just be built; it is expected that tests are implemented such that failures cause the build to fail via elaboration-time errors.
:::

```lakeHelp lint
Lint the workspace's root package using its configured lint driver

USAGE:
  lake lint [-- <args>...]

A lint driver can be configured by either setting the `lintDriver` package
configuration option by tagging a script or executable `@[lint_driver]`.
A definition in dependency can be used as a test driver by using the
`<pkg>/<name>` syntax for the 'testDriver' configuration option.

A script lint driver will be run with the  package configuration's
`lintDriverArgs` plus the CLI `args`. An executable lint driver will be
built and then run like a script.

```

:::lake lint " [\"--\" args...]"

Lint the workspace's root package using its configured lint driver

A script lint driver will be run with the  package configuration's
`lintDriverArgs` plus the CLI `args`. An executable lint driver will be
built and then run like a script.
:::

```lakeHelp "check-test"
Check if there is a properly configured test driver

USAGE:
  lake check-test

Exits with code 0 if the workspace's root package has a properly
configured lint driver. Errors (with code 1) otherwise.

Does NOT verify that the configured test driver actually exists in the
package or its dependencies. It merely verifies that one is specified.

```

:::lake «check-test»

Check if there is a properly configured test driver

Exits with code 0 if the workspace's root package has a properly
configured lint driver. Errors (with code 1) otherwise.

Does NOT verify that the configured test driver actually exists in the
package or its dependencies. It merely verifies that one is specified.

This is useful for distinguishing between failing tests and incorrectly configured packages.
:::

```lakeHelp "check-lint"
Check if there is a properly configured lint driver

USAGE:
  lake check-lint

Exits with code 0 if the workspace's root package has a properly
configured lint driver. Errors (with code 1) otherwise.

Does NOT verify that the configured lint driver actually exists in the
package or its dependencies. It merely verifies that one is specified.

```

:::lake «check-lint»
Check if there is a properly configured lint driver

Exits with code 0 if the workspace's root package has a properly
configured lint driver. Errors (with code 1) otherwise.

Does NOT verify that the configured lint driver actually exists in the
package or its dependencies. It merely verifies that one is specified.

This is useful for distinguishing between failing lints and incorrectly configured packages.
:::


## Scripts

```lakeHelp script
Manage Lake scripts

USAGE:
  lake script <COMMAND>

COMMANDS:
  list                  list available scripts
  run <script>          run a script
  doc <script>          print the docstring of a given script

See `lake help <command>` for more information on a specific command.
```

```lakeHelp scripts
List available scripts

USAGE:
  lake script list

ALIAS: lake scripts

This command prints the list of all available scripts in the workspace.
```

:::lake script list (alias := scripts)
Lists the available {ref "lake-scripts"}[scripts] in the workspace.
:::

```lakeHelp run
Run a script

USAGE:
  lake script run [[<package>/]<script>] [<args>...]

ALIAS: lake run

This command runs the `script` of the workspace (or the specific `package`),
passing `args` to it.

A bare `lake run` command will run the default script(s) of the root package
(with no arguments).
```

:::lake script run "[[package\"/\"]script [args...]]" (alias := run)
This command runs the {lakeMeta}`script` of the workspace (or the specified {lakeMeta}`package`),
passing {lakeMeta}`args` to it.

A bare {lake}`run` command will run the default script(s) of the root package(with no arguments).
:::

:::lake script doc "script"
Prints the documentation comment for {lakeMeta}`script`.
:::



## Language Server

```lakeHelp serve
Start the Lean language server

USAGE:
  lake serve [-- <args>...]

Run the language server of the Lean installation (i.e., via `lean --server`)
with the package configuration's `moreServerArgs` field and `args`.

```

:::lake serve "[\"--\" args...]"
Runs the Lean language server in the workspace's root project with the {tech}[package configuration]'s `moreServerArgs` field and {lakeMeta}`args`.

This command is typically invoked by editors or other tooling, rather than manually.
:::

# Dependency Management

```lakeHelp update
Update dependencies and save them to the manifest

USAGE:
  lake update [<package>...]

ALIAS: lake upgrade

Updates the Lake package manifest (i.e., `lake-manifest.json`),
downloading and upgrading packages as needed. For each new (transitive) git
dependency, the appropriate commit is cloned into a subdirectory of
`packagesDir`. No copy is made of local dependencies.

If a set of packages are specified, said dependencies are upgraded to
the latest version compatible with the package's configuration (or removed if
removed from the configuration). If there are dependencies on multiple versions
of the same package, the version materialized is undefined.

A bare `lake update` will upgrade all dependencies.
```

:::lake update "[packages...]"
Updates the Lake package {tech}[manifest] (i.e., `lake-manifest.json`), downloading and upgrading packages as needed.
For each new (transitive) {tech}[Git dependency], the appropriate commit is cloned into a subdirectory of the workspace's {tech}[package directory].
No copy is made of local dependencies.

If a set of packages {lakeMeta}`packages` is specified, then these dependencies are upgraded to the latest version compatible with the package's configuration (or removed if removed from the configuration).
If there are dependencies on multiple versions of the same package, an arbitrary version is selected.

A bare {lake}`update` will upgrade all dependencies.
:::

# Packaging and Distribution

```lakeHelp "upload"
Upload build artifacts to a GitHub release

USAGE:
  lake upload <tag>

Packs the root package's `buildDir` into a `tar.gz` archive using `tar` and
then uploads the asset to the pre-existing GitHub release `tag` using `gh`.
```

:::lake upload "tag"
Packs the root package's `buildDir` into a `tar.gz` archive using `tar` and then uploads the asset to the pre-existing [GitHub](https://github.com) release {lakeMeta}`tag` using [`gh`](https://cli.github.com/).
Other hosts are not yet supported.
:::

## Cached Cloud Builds

**These commands are still experimental.**
They are likely change in future versions of Lake based on user feedback.
Packages that use cloud build archives should enable the {tomlField Lake.PackageConfig}`platformIndependent` setting.

```lakeHelp "pack"
Pack build artifacts into a archive for distribution

USAGE:
  lake pack [<file.tgz>]

Packs the root package's `buildDir` into a gzip tar archive using `tar`.
If a path for the archive is not specified, creates a archive in the package's
Lake directory (`.lake`) named according to its `buildArchive` setting.

Does NOT build any artifacts. It just packs the existing ones.
```

:::lake pack "[archive.tar.gz]"
Packs the root package's {tech}[build directory] into a gzipped tar archive using `tar`.
If a path for the archive is not specified, the archive in the package's Lake directory (`.lake`) and named according to its `buildArchive` setting.
This command does not build any artifacts: it only archives what is present.
Users should ensure that the desired artifacts are present before running this command.
:::

```lakeHelp "unpack"
Unpack build artifacts from a distributed archive

USAGE:
  lake unpack [<file.tgz>]

Unpack build artifacts from the gzip tar archive `file.tgz` into the root
package's `buildDir`. If a path for the archive is not specified, uses the
the package's `buildArchive` in its Lake directory (`.lake`).
```

:::lake unpack "[archive.tar.gz]"
Unpacks the contents of the gzipped tar archive {lakeMeta}`archive.tgz` into the root package's {tech}[build directory].
If {lakeMeta}`archive.tgz` is not specified, the package's `buildArchive` setting is used to determine a filename, and the file is expected in package's Lake directory (`.lake`).
:::




# Configuration Files


```lakeHelp "translate-config"
Translate a Lake configuration file into a different language

USAGE:
  lake translate-config <lang> [<out-file>]

Translates the loaded package's configuration into another of
Lake's supported configuration languages (i.e., either `lean` or `toml`).
The produced file is written to `out-file` or, if not provided, the path of
the configuration file with the new language's extension. If the output file
already exists, Lake will error.

Translation is lossy. It does not preserve comments or formatting and
non-declarative configuration will be discarded.
```

:::lake «translate-config» "lang [«out-file»]"
Translates the loaded package's configuration into another of Lake's supported configuration languages (i.e., either `lean` or `toml`).
The produced file is written to `out-file` or, if not provided, the path of the configuration file with the new language's extension.
If the output file already exists, Lake will error.

Translation is lossy.
It does not preserve comments or formatting and non-declarative configuration is discarded.
:::
