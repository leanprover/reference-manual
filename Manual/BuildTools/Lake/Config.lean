/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Command
import Lake.DSL.Syntax
import Lake.Config.Monad

import Manual.Meta
import Manual.BuildTools.Lake.CLI


open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

open Lake.DSL

#doc (Manual) "Configuration File Format" =>
%%%
tag := "lake-config"
%%%

:::paragraph
Lake offers two formats for {tech}[package configuration] files:

: TOML

  The TOML configuration format is fully declarative.
  Projects that don't include custom targets, facets, or scripts can use the TOML format.
  Because TOML parsers are available for a wide variety of languages, using this format facilitates integration with tools that are not written in Lean.

: Lean

  The Lean configuration format is more flexible and allows for custom targets, facets, and scripts.
  It features an embedded domain-specific language for describing the declarative subset of configuration options that is available from the TOML format.
  Additionally, the Lake API can be used to express build configurations that are outside of the possibilities of the declarative options.

The command {lake}`translate-config` can be used to automatically convert between the two formats.
:::

Both formats are processed similarly by Lake, which extracts the {tech}[package configuration] from the configuration file in the form of internal structure types.
When the package is {tech key:="configure package"}[configured], the resulting data structures are written to `lakefile.olean` in the {tech}[build directory].


# Declarative TOML Format
%%%
tag := "lake-config-toml"
%%%


TOML{margin}[[_Tom's Obvious Minimal Language_](https://toml.io/en/) is a standardized format for configuration files.] configuration files describe the most-used, declarative subset of Lake {tech}[package configuration] files.
TOML files denote _tables_, which map keys to values.
Values may consist of strings, numbers, arrays of values, or further tables.
Because TOML allows considerable flexibility in file structure, this reference documents the values that are expected rather than the specific syntax used to produce them.

The contents of `lakefile.toml` should denote a TOML table that describes a Lean package.
This configuration consists of both scalar fields that describe the entire package, as well as the following fields that contain arrays of further tables:
 * `require`
 * `lean_lib`
 * `lean_exe`

Fields that are not part of the configuration tables described here are presently ignored.
To reduce the risk of typos, this is likely to change in the future.
Field names not used by Lake should not be used to store metadata to be processed by other tools.


## Package Configuration

The top-level contents of `lakefile.toml` specify the options that apply to the package itself, including metadata such as the name and version, the locations of the files in the {tech}[workspace], compiler flags to be used for all {tech}[targets], and
The only mandatory field is `name`, which declares the package's name.

::::tomlTableDocs root "Package Configuration" Lake.PackageConfig skip:=backend skip:=releaseRepo? skip:=buildArchive? skip:=manifestFile skip:=moreServerArgs skip:=dynlibs skip:=plugins

:::tomlFieldCategory "Metadata" name version versionTags description keywords homepage license licenseFiles readmeFile reservoir
These options describe the package.
They are used by [Reservoir](https://reservoir.lean-lang.org/) to index and display packages.
If a field is left out, Reservoir may use information from the package's GitHub repository to fill in details.
:::

:::tomlFieldCategory "Layout" packagesDir srcDir buildDir leanLibDr nativeLibDir binDir irDir
These options control the top-level directory layout of the package and its build directory.
Further paths specified by libraries, executables, and targets within the package are relative to these directories.
:::

:::tomlFieldCategory "Building and Running" defaultTargets leanLibDir platformIndependent precompileModules moreServerOptions moreGlobalServerArgs buildType leanOptions moreLeanArgs weakLeanArgs moreLeancArgs weakLeancArgs moreLinkArgs weakLinkArgs extraDepTargets

These options configure how code is built and run in the package.
Libraries, executables, and other {tech}[targets] within a package can further add to parts of this configuration.

:::

:::tomlFieldCategory "Testing and Linting" testDriver testDriverArgs lintDriver lintDriverArgs

The CLI commands {lake}`test` and {lake}`lint` use definitions configured by the {tech}[workspace]'s {tech}[root package] to perform testing and linting.
The code that is run to perform tests and lits are referred to as the test or lint driver.
In Lean configuration files, these can be specified by applying the `@[test_driver]` or `@[lint_driver]` attributes to a {tech}[Lake script] or an executable or library target.
In both Lean and TOML configuration files, they can also be configured by setting these options.
A target or script `TGT` from a dependency `PKG` can be specified as a test or lint driver using the string `"PKG/TGT"`

:::

:::tomlFieldCategory "Cloud Releases" releaseRepo buildArchive preferReleaseBuild

These options define a cloud release for the package, as described in the section on {ref "lake-github"}[GitHub release builds].

:::

:::tomlField Lake.PackageConfig defaultTargets "default targets' names (array)" "default targets' names (array)" String (sort := 2)

{includeDocstring Lake.Package.defaultTargets (elab:=false)}

:::

::::

:::::example "Minimal TOML Package Configuration"
The minimal TOML configuration for a Lean {tech}[package] sets only the package's name, using the default values for all other fields.
This package contains no {tech}[targets], so there is no code to be built.

::::lakeToml Lake.PackageConfig _root_
```toml
name = "example-package"
```
```expected
{name := `«example-package»,
  dir := FilePath.mk ".",
  relDir := FilePath.mk ".",
  config :=
    {toWorkspaceConfig := { packagesDir := FilePath.mk ".lake/packages" },
      toLeanConfig :=
        { buildType := Lake.BuildType.release,
          leanOptions := #[],
          moreLeanArgs := #[],
          weakLeanArgs := #[],
          moreLeancArgs := #[],
          moreServerOptions := #[],
          weakLeancArgs := #[],
          moreLinkObjs := #[],
          moreLinkLibs := #[],
          moreLinkArgs := #[],
          weakLinkArgs := #[],
          backend := Lake.Backend.default,
          platformIndependent := none,
          dynlibs := #[],
          plugins := #[] },
      bootstrap := false,
      manifestFile := none,
      extraDepTargets := #[],
      precompileModules := false,
      moreGlobalServerArgs := #[],
      srcDir := FilePath.mk ".",
      buildDir := FilePath.mk ".lake/build",
      leanLibDir := FilePath.mk "lib/lean",
      nativeLibDir := FilePath.mk "lib",
      binDir := FilePath.mk "bin",
      irDir := FilePath.mk "ir",
      releaseRepo := none,
      buildArchive := ELIDED,
      preferReleaseBuild := false,
      testDriver := "",
      testDriverArgs := #[],
      lintDriver := "",
      lintDriverArgs := #[],
      version := { toSemVerCore := { major := 0, minor := 0, patch := 0 }, specialDescr := "" },
      versionTags := { filter := #<fun>, name := `default, descr? := none},
      description := "",
      keywords := #[],
      homepage := "",
      license := "",
      licenseFiles := #[FilePath.mk "LICENSE"],
      readmeFile := FilePath.mk "README.md",
      reservoir := true},
  configFile := FilePath.mk "lakefile",
  relConfigFile := FilePath.mk "lakefile",
  relManifestFile := FilePath.mk "lake-manifest.json",
  scope := "",
  remoteUrl := "",
  depConfigs := #[],
  targetDecls := #[],
  targetDeclMap := {},
  defaultTargets := #[],
  scripts := {},
  defaultScripts := #[],
  postUpdateHooks := #[],
  buildArchive := ELIDED,
  testDriver := "",
  lintDriver := ""}
```
::::
:::::

:::::example "Library TOML Package Configuration"
The minimal TOML configuration for a Lean {tech}[package] sets the package's name and defines a library target.
This library is named `Sorting`, and its modules are expected under the `Sorting.*` hierarchy.
::::lakeToml Lake.PackageConfig _root_
```toml
name = "example-package"
defaultTargets = ["Sorting"]

[[lean_lib]]
name = "Sorting"
```
```expected
{name := `«example-package»,
  dir := FilePath.mk ".",
  relDir := FilePath.mk ".",
  config :=
    {toWorkspaceConfig := { packagesDir := FilePath.mk ".lake/packages" },
      toLeanConfig :=
        { buildType := Lake.BuildType.release,
          leanOptions := #[],
          moreLeanArgs := #[],
          weakLeanArgs := #[],
          moreLeancArgs := #[],
          moreServerOptions := #[],
          weakLeancArgs := #[],
          moreLinkObjs := #[],
          moreLinkLibs := #[],
          moreLinkArgs := #[],
          weakLinkArgs := #[],
          backend := Lake.Backend.default,
          platformIndependent := none,
          dynlibs := #[],
          plugins := #[] },
      bootstrap := false,
      manifestFile := none,
      extraDepTargets := #[],
      precompileModules := false,
      moreGlobalServerArgs := #[],
      srcDir := FilePath.mk ".",
      buildDir := FilePath.mk ".lake/build",
      leanLibDir := FilePath.mk "lib/lean",
      nativeLibDir := FilePath.mk "lib",
      binDir := FilePath.mk "bin",
      irDir := FilePath.mk "ir",
      releaseRepo := none,
      buildArchive := ELIDED,
      preferReleaseBuild := false,
      testDriver := "",
      testDriverArgs := #[],
      lintDriver := "",
      lintDriverArgs := #[],
      version := { toSemVerCore := { major := 0, minor := 0, patch := 0 }, specialDescr := "" },
      versionTags := { filter := #<fun>, name := `default, descr? := none},
      description := "",
      keywords := #[],
      homepage := "",
      license := "",
      licenseFiles := #[FilePath.mk "LICENSE"],
      readmeFile := FilePath.mk "README.md",
      reservoir := true},
  configFile := FilePath.mk "lakefile",
  relConfigFile := FilePath.mk "lakefile",
  relManifestFile := FilePath.mk "lake-manifest.json",
  scope := "",
  remoteUrl := "",
  depConfigs := #[],
  targetDecls :=
    #[{toConfigDecl :=
          {pkg := `«example-package»,
            name := `Sorting,
            kind := `lean_lib,
            config :=
              {toLeanConfig :=
                  { buildType := Lake.BuildType.release,
                    leanOptions := #[],
                    moreLeanArgs := #[],
                    weakLeanArgs := #[],
                    moreLeancArgs := #[],
                    moreServerOptions := #[],
                    weakLeancArgs := #[],
                    moreLinkObjs := #[],
                    moreLinkLibs := #[],
                    moreLinkArgs := #[],
                    weakLinkArgs := #[],
                    backend := Lake.Backend.default,
                    platformIndependent := none,
                    dynlibs := #[],
                    plugins := #[] },
                srcDir := FilePath.mk ".",
                roots := #[`Sorting],
                globs := #[Lake.Glob.one `Sorting],
                libName := "Sorting",
                needs := #[],
                extraDepTargets := #[],
                precompileModules := false,
                defaultFacets := #[`lean_lib.leanArts],
                nativeFacets := #<fun>},
            wf_data := …},
        pkg_eq := …}],
  targetDeclMap :=
    {`Sorting ↦
        {toPConfigDecl :=
            {toConfigDecl :=
                {pkg := `«example-package»,
                  name := `Sorting,
                  kind := `lean_lib,
                  config :=
                    {toLeanConfig :=
                        { buildType := Lake.BuildType.release,
                          leanOptions := #[],
                          moreLeanArgs := #[],
                          weakLeanArgs := #[],
                          moreLeancArgs := #[],
                          moreServerOptions := #[],
                          weakLeancArgs := #[],
                          moreLinkObjs := #[],
                          moreLinkLibs := #[],
                          moreLinkArgs := #[],
                          weakLinkArgs := #[],
                          backend := Lake.Backend.default,
                          platformIndependent := none,
                          dynlibs := #[],
                          plugins := #[] },
                      srcDir := FilePath.mk ".",
                      roots := #[`Sorting],
                      globs := #[Lake.Glob.one `Sorting],
                      libName := "Sorting",
                      needs := #[],
                      extraDepTargets := #[],
                      precompileModules := false,
                      defaultFacets := #[`lean_lib.leanArts],
                      nativeFacets := #<fun>},
                  wf_data := …},
              pkg_eq := …},
          name_eq := …},
      },
  defaultTargets := #[`Sorting],
  scripts := {},
  defaultScripts := #[],
  postUpdateHooks := #[],
  buildArchive := ELIDED,
  testDriver := "",
  lintDriver := ""}
```
::::
:::::

## Dependencies

Dependencies are specified in the {toml}`[[require]]` field array of a package configuration, which specifies both the name and the source of each package.
There are three kinds of sources:
 * [Reservoir](https://reservoir.lean-lang.org/), or an alternative package registry
 * Git repositories, which may be local paths or URLs
 * Local paths

::::tomlTableDocs "require" "Requiring Packages" Lake.Dependency skip:=src? skip := opts skip:=subdir skip:=version?

The {tomlField Lake.Dependency}`path` and {tomlField Lake.Dependency}`git` fields specify an explicit source for a dependency.
If neither are provided, then the dependency is fetched from [Reservoir](https://reservoir.lean-lang.org/), or an alternative registry if one has been configured.
The {tomlField Lake.Dependency}`scope` field is required when fetching a package from Reservoir.

:::tomlField Lake.Dependency path "Path" "Paths" System.FilePath
A dependency on the local filesystem, specified by its path.
:::

:::tomlField Lake.Dependency git "Git specification" "Git specifications" Lake.DependencySrc
A dependency in a Git repository, specified either by its URL as a string or by a table with the keys:
 * `url`: the repository URL
 * `subDir`: the subdirectory of the Git repository that contains the package's source code
:::

:::tomlField Lake.Dependency rev "Git revision" "Git revisions" String
For Git or Reservoir dependencies, this field specifies the Git revision, which may be a branch name, a tag name, or a specific hash.
On Reservoir, the `version` field takes precedence over this field.
:::

:::tomlField Lake.Dependency source "Package Source" "Package Sources" Lake.DependencySrc
A dependency source, specified as a self-contained table, which is used when neither the `git` nor the `path` key is present.
The key `type` should be either the string `"git"` or the string `"path"`.
If the type is `"path"`, then there must be a further key `"path"` whose value is a string that provides the location of the package on disk.
If the type is `"git"`, then the following keys should be present:
 * `url`: the repository URL
 * `rev`: the Git revision, which may be a branch name, a tag name, or a specific hash (optional)
 * `subDir`: the subdirectory of the Git repository that contains the package's source code
:::

:::tomlField Lake.Dependency version "version as string" "versions as strings" String

{includeDocstring Lake.Dependency.version?}

:::

::::

:::::example "Requiring Packages from Reservoir"
The package `example` can be required from Reservoir using this TOML configuration:
::::lakeToml Lake.Dependency require
```toml
[[require]]
name = "example"
version = "2.12"
scope = "exampleDev"
```
```expected
#[{name := `example, scope := "exampleDev", version? := some "2.12", src? := none, opts := {}}]
```
::::
:::::

:::::example "Requiring Packages from Git"
The package `example` can be required from a Git repository using this TOML configuration:
::::lakeToml Lake.Dependency require
```toml
[[require]]
name = "example"
git = "https://git.example.com/example.git"
rev = "main"
version = "2.12"
```
```expected
#[{name := `example,
    scope := "",
    version? := some "2.12",
    src? := some (Lake.DependencySrc.git "https://git.example.com/example.git" (some "main") none),
    opts := {}}]
```
::::

In particular, the package will be checked out from the `main` branch, and the version number specified in the package's {tech key:="package configuration"}[configuration] should match `2.12`.
:::::

:::::example "Requiring Packages from a Git tag"
The package `example` can be required from the tag `v2.12` in a Git repository using this TOML configuration:
::::lakeToml Lake.Dependency require
```toml
[[require]]
name = "example"
git = "https://git.example.com/example.git"
rev = "v2.12"
```
```expected
#[{name := `example,
    scope := "",
    version? := none,
    src? := some (Lake.DependencySrc.git "https://git.example.com/example.git" (some "v2.12") none),
    opts := {}}]
```
::::
The version number specified in the package's {tech key:="package configuration"}[configuration] is not used.
:::::

:::::example "Requiring Reservoir Packages from a Git tag"
The package `example`, found using Reservoir, can be required from the tag `v2.12` in its Git repository using this TOML configuration:
::::lakeToml Lake.Dependency require
```toml
[[require]]
name = "example"
rev = "v2.12"
scope = "exampleDev"
```
```expected
#[{name := `example, scope := "exampleDev", version? := some "git#v2.12", src? := none, opts := {}}]
```
::::
The version number specified in the package's {tech key:="package configuration"}[configuration] is not used.
:::::

:::::example "Requiring Packages from Paths"
The package `example` can be required from the local path `../example` using this TOML configuration:
::::lakeToml Lake.Dependency require
```toml
[[require]]
name = "example"
path = "../example"
```
```expected
#[{name := `example,
    scope := "",
    version? := none,
    src? := some (Lake.DependencySrc.path (FilePath.mk "../example")),
    opts := {}}]
```
::::
Dependencies on local paths are useful when developing multiple packages in a single repository, or when testing whether a change to a dependency fixes a bug in a downstream package.
:::::

:::::example "Sources as Tables"
The information about the package source can be written in an explicit table.
::::lakeToml Lake.Dependency require
```toml
[[require]]
name = "example"
source = {type = "git", url = "https://example.com/example.git"}
```
```expected
#[{name := `example,
    scope := "",
    version? := none,
    src? := some (Lake.DependencySrc.git "https://example.com/example.git" none none),
    opts := {}}]
```
::::
:::::

## Library Targets

Library targets are expected in the `lean_lib` array of tables.

::::tomlTableDocs "lean_lib" "Library Targets" Lake.LeanLibConfig skip := backend skip:=globs skip:=nativeFacets
::::

:::::example "Minimal Library Target"
This library declaration supplies only a name:
::::lakeToml Lake.LeanLibConfig lean_lib
```toml
[[lean_lib]]
name = "TacticTools"
```
```expected
#[{ name := TacticTools,
    val := {toLeanConfig :=
        { buildType := Lake.BuildType.release,
          leanOptions := #[],
          moreLeanArgs := #[],
          weakLeanArgs := #[],
          moreLeancArgs := #[],
          moreServerOptions := #[],
          weakLeancArgs := #[],
          moreLinkObjs := #[],
          moreLinkLibs := #[],
          moreLinkArgs := #[],
          weakLinkArgs := #[],
          backend := Lake.Backend.default,
          platformIndependent := none,
          dynlibs := #[],
          plugins := #[] },
      srcDir := FilePath.mk ".",
      roots := #[`TacticTools],
      globs := #[Lake.Glob.one `TacticTools],
      libName := "TacticTools",
      needs := #[],
      extraDepTargets := #[],
      precompileModules := false,
      defaultFacets := #[`lean_lib.leanArts],
      nativeFacets := #<fun>}}]
```
::::
The library's source is located in the package's default source directory, in the module hierarchy rooted at `TacticTools`.
:::::

:::::example "Configured Library Target"
This library declaration supplies more options:
::::lakeToml Lake.LeanLibConfig lean_lib
```toml
[[lean_lib]]
name = "TacticTools"
srcDir = "src"
precompileModules = true
```
```expected
#[{ name := TacticTools,
    val := {toLeanConfig :=
        { buildType := Lake.BuildType.release,
          leanOptions := #[],
          moreLeanArgs := #[],
          weakLeanArgs := #[],
          moreLeancArgs := #[],
          moreServerOptions := #[],
          weakLeancArgs := #[],
          moreLinkObjs := #[],
          moreLinkLibs := #[],
          moreLinkArgs := #[],
          weakLinkArgs := #[],
          backend := Lake.Backend.default,
          platformIndependent := none,
          dynlibs := #[],
          plugins := #[] },
      srcDir := FilePath.mk "src",
      roots := #[`TacticTools],
      globs := #[Lake.Glob.one `TacticTools],
      libName := "TacticTools",
      needs := #[],
      extraDepTargets := #[],
      precompileModules := true,
      defaultFacets := #[`lean_lib.leanArts],
      nativeFacets := #<fun>}}]
```
::::
The library's source is located in the directory `src`, in the module hierarchy rooted at `TacticTools`.
If its modules are accessed at elaboration time, they will be compiled to native code and linked in, rather than run in the interpreter.
:::::

## Executable Targets

:::: tomlTableDocs "lean_exe" "Executable Targets" Lake.LeanExeConfig skip := backend skip:=globs skip:=nativeFacets

::::

:::::example "Minimal Executable Target"
This executable declaration supplies only a name:
::::lakeToml Lake.LeanExeConfig lean_exe
```toml
[[lean_exe]]
name = "trustworthytool"
```
```expected
#[{ name := trustworthytool,
    val := {toLeanConfig :=
        { buildType := Lake.BuildType.release,
          leanOptions := #[],
          moreLeanArgs := #[],
          weakLeanArgs := #[],
          moreLeancArgs := #[],
          moreServerOptions := #[],
          weakLeancArgs := #[],
          moreLinkObjs := #[],
          moreLinkLibs := #[],
          moreLinkArgs := #[],
          weakLinkArgs := #[],
          backend := Lake.Backend.default,
          platformIndependent := none,
          dynlibs := #[],
          plugins := #[] },
      srcDir := FilePath.mk ".",
      root := `trustworthytool,
      exeName := "trustworthytool",
      needs := #[],
      extraDepTargets := #[],
      supportInterpreter := false,
      nativeFacets := #<fun>}}]
```
::::

```lean (show := false)
def main : List String → IO UInt32 := fun _ => pure 0
```

The executable's {lean}`main` function is expected in a module named `trustworthytool.lean` in the package's default source file path.
The resulting executable is named `trustworthytool`.
:::::

:::::example "Configured Executable Target"
The name `trustworthy-tool` is not a valid Lean name due to the dash (`-`).
To use this name for an executable target, an explicit module root must be supplied.
Even though `trustworthy-tool` is a perfectly acceptable name for an executable, the target also specifies that the result of compilation and linking should be named `tt`.

::::lakeToml Lake.LeanExeConfig lean_exe
```toml
[[lean_exe]]
name = "trustworthy-tool"
root = "TrustworthyTool"
exeName = "tt"
```
```expected
#[{ name := «trustworthy-tool»,
    val := {toLeanConfig :=
        { buildType := Lake.BuildType.release,
          leanOptions := #[],
          moreLeanArgs := #[],
          weakLeanArgs := #[],
          moreLeancArgs := #[],
          moreServerOptions := #[],
          weakLeancArgs := #[],
          moreLinkObjs := #[],
          moreLinkLibs := #[],
          moreLinkArgs := #[],
          weakLinkArgs := #[],
          backend := Lake.Backend.default,
          platformIndependent := none,
          dynlibs := #[],
          plugins := #[] },
      srcDir := FilePath.mk ".",
      root := `TrustworthyTool,
      exeName := "tt",
      needs := #[],
      extraDepTargets := #[],
      supportInterpreter := false,
      nativeFacets := #<fun>}}]
```
::::

```lean (show := false)
def main : List String → IO UInt32 := fun _ => pure 0
```

The executable's {lean}`main` function is expected in a module named `TrustworthyTool.lean` in the package's default source file path.
:::::

# Lean Format
%%%
tag := "lake-config-lean"
%%%


The Lean format for Lake {tech}[package configuration] files provides a domain-specific language for the declarative features that are supported in the TOML format.
Additionally, it provides the ability to write Lean code to implement any necessary build logic that is not expressible declaratively.

Because the Lean format is a Lean source file, it can be edited using all the features of the Lean language server.
Additionally, Lean's metaprogramming framework allows elaboration-time side effects to be used to implement features such as configuration steps that are conditional on the current platform.
However, a consequence of the Lean configuration format being a Lean file is that it is not feasible to process such files using tools that are not themselves written in Lean.

```lean (show := false)
section
open Lake DSL
open Lean (NameMap)
```

## Declarative Fields

The declarative subset of the Lean configuration format uses sequences of declaration fields to specify configuration options.

:::syntax Lake.DSL.declField (title := "Declarative Fields") (open := false)

{includeDocstring Lake.DSL.declField}

```grammar
$_ := $_
```
:::

## Packages
::::syntax command title:="Package Configuration"
```grammar
$[$_:docComment]?
$[@[ $_,* ]]?
package $name:identOrStr
```

```grammar
$[$_:docComment]?
$[@[$_,*]]?
package $name where
  $item*
```

```grammar
$[$_:docComment]?
$[@[$_,*]]?
package $_:identOrStr {
  $[$_:declField];*
}
$[where
  $[$_:letRecDecl];*]?
```

There can only be one {keywordOf Lake.DSL.packageCommand}`package` declaration per Lake configuration file.
The defined package configuration will be available for reference as `_package`.

::::

::::syntax command (title := "Post-Update Hooks")
```grammar
post_update $[$name]? $v
```

{includeDocstring Lake.DSL.postUpdateDecl}

::::


## Dependencies

Dependencies are specified using the {keywordOf Lake.DSL.requireDecl}`require` declaration.

:::syntax command (title := "Requiring Packages")
```grammar
$doc:docComment
require $name:depName $[@ $[git]? $_:term]? $[$_:fromClause]? $[with $_:term]?
```

The `@` clause specifies a package version, which is used when requiring a package from [Reservoir](https://reservoir.lean-lang.org/).
The version may either be a string that specifies the version declared in the package's {name Lake.PackageConfig.version}`version` field, or a specific Git revision.
Git revisions may be branch names, tag names, or commit hashes.

The optional {syntaxKind}`fromClause` specifies a package source other than Reservoir, which may be either a Git repository or a local path.

The {keywordOf Lake.DSL.requireDecl}`with` clause specifies a {lean}`NameMap String` of Lake options that will be used to configure the dependency.
This is equivalent to passing {lakeOpt}`-K` options to {lake}`build` when building the dependency on the command line.
:::

:::syntax fromClause (open := false) (title := "Package Sources")

{includeDocstring Lake.DSL.fromClause}

```grammar
from $t:term
```

```grammar
from git $t $[@ $t]? $[/ $t]?
```

:::


## Targets

{tech}[Targets] are typically added to the set of default targets by applying the `default_target` attribute, rather than by explicitly listing them.

:::TODO
It's presently impossible to import Lake.DSL.AttributesCore due to initialization changes, so `default_target` can't be rendered/checked as an attribute above. This should be fixed upstream.
:::

:::syntax attr (title := "Specifying Default Targets") (label := "attribute")

```grammar
default_target
```
Marks a target as a default, to be built when no other target is specified.
:::

### Libraries


:::syntax command (title := "Library Targets")

To define a library in which all configurable fields have their default values, use {keywordOf Lake.DSL.leanLibCommand}`lean_lib` with no further fields.

```grammar
$[$_:docComment]?
$[$_:attributes]?
lean_lib $_:identOrStr
```

The default configuration can be modified by providing the new values.

```grammar
$[$_:docComment]?
$[$_:attributes]?
lean_lib $_:identOrStr where
  $field*
```


```grammar
$[$_:docComment]?
$[$_:attributes]?
lean_lib $_:identOrStr {
  $[$_:declField];*
}
$[where
  $[$_:letRecDecl];*]?
```
:::

The fields of {keywordOf Lake.DSL.leanLibCommand}`lean_lib` are those of the {name Lake.LeanLibConfig}`LeanLibConfig` structure.

{docstring Lake.LeanLibConfig}

### Executables

:::syntax command (title := "Executable Targets")

To define an executable in which all configurable fields have their default values, use {keywordOf Lake.DSL.leanExeCommand}`lean_exe` with no further fields.

```grammar
$[$_:docComment]? $[$_:attributes]?
lean_exe $_:identOrStr
```

The default configuration can be modified by providing the new values.

```grammar
$[$_:docComment]? $[$_:attributes]?
lean_exe $_:identOrStr where
  $field*
```

```grammar
$[$_:docComment]? $[$_:attributes]?
lean_exe $_:identOrStr {
  $[$_:declField];*
}
$[where
  $[$_:letRecDecl];*]?
```
:::

The fields of {keywordOf Lake.DSL.leanExeCommand}`lean_exe` are those of the {name Lake.LeanExeConfig}`LeanExeConfig` structure.

{docstring Lake.LeanExeConfig}

### External Libraries

Because external libraries may be written in any language and require arbitrary build steps, they are defined as programs written in the {name Lake.FetchM}`FetchM` monad that produce a {name Lake.Job}`Job`.
External library targets should produce a build job that carries out the build and then returns the location of the resulting static library.
For the external library to link properly when {name Lake.PackageConfig.precompileModules}`precompileModules` is on, the static library produced by an {keyword}`extern_lib` target must follow the platform's naming conventions for libraries (i.e., be named foo.a on Windows or libfoo.a on Unix-like systems).
The utility function {name}`Lake.nameToStaticLib` converts a library name into its proper file name for current platform.

:::syntax command (title := "External Library Targets")

```grammar
$[$_:docComment]?
$[$_:attributes]?
extern_lib $_:identOrStr $_? := $_:term
$[where $_*]?
```

{includeDocstring Lake.DSL.externLibCommand}

:::

### Custom Targets

Custom targets may be used to define any incrementally-built artifact whatsoever, using the Lake API.

:::syntax command (title := "Custom Targets")

```grammar
$[$_:docComment]?
$[$_:attributes]?
target $_:identOrStr $_? : $ty:term := $_:term
$[where $_*]?
```

{includeDocstring Lake.DSL.externLibCommand}

:::

### Custom Facets

Custom facets allow additional artifacts to be incrementally built from a module, library, or package.


:::syntax command (title := "Custom Package Facets")

Package facets allow the production of an artifact or set of artifacts from a whole package.
The Lake API makes it possible to query a package for its libraries; thus, one common use for a package facet is to build a given facet of each library.

```grammar
$[$_:docComment]?
$[@[$_,*]]?
package_facet $_:identOrStr $_? : $ty:term := $_:term
$[where $_*]?
```

{includeDocstring Lake.DSL.packageFacetDecl}

:::

:::syntax command (title := "Custom Library Facets")

Package facets allow the production of an artifact or set of artifacts from a library.
The Lake API makes it possible to query a library for its modules; thus, one common use for a library facet is to build a given facet of each module.

```grammar
$[$_:docComment]?
$[@[$_,*]]?
library_facet $_:identOrStr $_? : $ty:term := $_:term
$[where $_*]?
```

{includeDocstring Lake.DSL.libraryFacetDecl}

:::

:::syntax command (title := "Custom Module Facets")

Package facets allow the production of an artifact or set of artifacts from a module, typically by invoking a command-line tool.

```grammar
$[$_:docComment]?
$[@[$_,*]]?
module_facet $_:identOrStr $_? : $ty:term := $_:term
$[where $_*]?
```

{includeDocstring Lake.DSL.moduleFacetDecl}

:::

## Configuration Value Types

{docstring Lake.BuildType}

In Lake's DSL, {deftech}_globs_ are patterns that match sets of module names.
There is a coercion from names to globs that match the name in question, and there are two postfix operators for constructing further globs.

```lean (show := false)
section
example : Lake.Glob := `n

/-- info: instCoeNameGlob -/
#check_msgs in
#synth Coe Lean.Name Lake.Glob

open Lake DSL

/-- info: Lake.Glob.andSubmodules `n -/
#check_msgs in
#eval show Lake.Glob from `n.*

/-- info: Lake.Glob.submodules `n -/
#check_msgs in
#eval show Lake.Glob from `n.+

end
```
:::freeSyntax term (title := "Glob Syntax")

The glob pattern `N.*` matches `N` or any submodule for which `N` is a prefix.

```grammar
$_:name".*"
```

The glob pattern `N.*` matches any submodule for which `N` is a strict prefix, but not `N` itself.

```grammar
$_:name".+"
```

Whitespace is not permitted between the name and `.*` or `.+`.

:::

{docstring Lake.Glob}



{docstring Lake.LeanOption (allowMissing := true)}

{docstring Lake.Backend}

## Scripts

Lake scripts are used to automate tasks that require access to a package configuration but do not participate in incremental builds of artifacts from code.
Scripts run in the {name Lake.ScriptM}`ScriptM` monad, which is {name}`IO` with an additional {tech}[reader monad] {tech key:="monad transformer"}[transformer] that provides access to the package configuration.
In particular, a script should have the type {lean}`List String → ScriptM UInt32`.
Workspace information in scripts is primarily accessed via the {inst}`MonadWorkspace ScriptM` instance.


```lean (show := false)
example : ScriptFn = (List String → ScriptM UInt32) := rfl
```

:::syntax command (title := "Script Declarations")
```grammar
$[$_:docComment]?
$[@[$_,*]]?
script $_:identOrStr $_? :=
  $_:term
$[where
  $_*]?
```

{includeDocstring Lake.DSL.scriptDecl}

:::

{docstring Lake.ScriptM}


:::syntax attr (label := "attribute") (title := "Default Scripts")
```grammar
default_script
```

Marks a {tech}[Lake script] as the {tech}[package]'s default.

:::



## Utilities

:::syntax term (title := "The Current Directory")
```grammar
__dir__
```

{includeDocstring Lake.DSL.dirConst}

:::

:::syntax term (title := "Configuration Options")
```grammar
get_config? $t
```

{includeDocstring Lake.DSL.getConfig}

:::

:::syntax command (title := "Compile-Time Conditionals")

```grammar
meta if $_ then
  $_
$[else $_]?
```

{includeDocstring Lake.DSL.metaIf}

:::

:::syntax cmdDo (title := "Command Sequences")

```grammar
  $_:command
```

```grammar
do
  $_:command
  $[$_:command]*
```

{includeDocstring Lake.DSL.cmdDo}

:::

:::syntax term (title := "Compile-Time Side Effects")
```grammar
run_io $t
```

{includeDocstring Lake.DSL.runIO}

:::
