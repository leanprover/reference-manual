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

open Manual
open Verso.Genre
open Verso.Genre.Manual

set_option pp.rawOnError true

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "Configuration File Format" =>
%%%
tag := "lake-config"
%%%

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


## Package Configuration

Package configurations provide many options.
The only mandatory field is `name`, which declares the package's name.

::::tomlTableDocs "Package Configuration" Lake.PackageConfig skip:=backend

:::tomlFieldCategory "Metadata" name version versionTags description keywords homepage license licenseFiles readmeFile reservoir
These options describe the package.
They are used by {ref "reservoir"}[Reservoir], to index and display packages.
If a field is left out, Reservoir may use information from the package's GitHub repository to fill in details.
:::

:::tomlFieldCategory "Layout" packagesDir srcDir buildDir leanLibDr nativeLibDir binDir irDir
These options control the top-level directory layout of the package and its build directory.
Further paths specified by libraries, executables, and targets within the package are relative to these directories.
:::

:::tomlFieldCategory "Building and Running" platformIndependent precompileModules moreServerOptions moreGlobalServerArgs buildType leanOptions moreLeanArgs weakLeanArgs moreLeancArgs weakLeancArgs moreLinkArgs weakLinkArgs extraDepTargets

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

:::tomlField Lake.PackageConfig defaultTargets "default targets' names (array)" String (sort := 2)

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
{dir := FilePath.mk "./.",
  relDir := FilePath.mk ".",
  config := {toWorkspaceConfig := { packagesDir := FilePath.mk ".lake/packages" },
    toLeanConfig := { buildType := Lake.BuildType.release,
      leanOptions := #[],
      moreLeanArgs := #[],
      weakLeanArgs := #[],
      moreLeancArgs := #[],
      moreServerOptions := #[],
      weakLeancArgs := #[],
      moreLinkArgs := #[],
      weakLinkArgs := #[],
      backend := Lake.Backend.default,
      platformIndependent := none },
    name := `«example-package»,
    manifestFile := none,
    extraDepTargets := #[],
    precompileModules := false,
    moreServerArgs := #[],
    moreGlobalServerArgs := #[],
    srcDir := FilePath.mk ".",
    buildDir := FilePath.mk ".lake/build",
    leanLibDir := FilePath.mk "lib",
    nativeLibDir := FilePath.mk "lib",
    binDir := FilePath.mk "bin",
    irDir := FilePath.mk "ir",
    releaseRepo? := none,
    releaseRepo := none,
    buildArchive? := none,
    buildArchive := ELIDED,
    preferReleaseBuild := false,
    testDriver := "",
    testDriverArgs := #[],
    lintDriver := "",
    lintDriverArgs := #[],
    version := { toSemVerCore := { major := 0, minor := 0, patch := 0 }, specialDescr := "" },
    versionTags := .satisfies #<fun> default,
    description := "",
    keywords := #[],
    homepage := "",
    license := "",
    licenseFiles := #[FilePath.mk "LICENSE"],
    readmeFile := FilePath.mk "README.md",
    reservoir := true},
  relConfigFile := FilePath.mk "lakefile",
  relManifestFile := FilePath.mk "lake-manifest.json",
  scope := "",
  remoteUrl := "",
  depConfigs := #[],
  leanLibConfigs := {},
  leanExeConfigs := {},
  externLibConfigs := {},
  opaqueTargetConfigs := {},
  defaultTargets := #[],
  scripts := {},
  defaultScripts := #[],
  postUpdateHooks := #[],
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
{dir := FilePath.mk "./.",
  relDir := FilePath.mk ".",
  config := {toWorkspaceConfig := { packagesDir := FilePath.mk ".lake/packages" },
    toLeanConfig := { buildType := Lake.BuildType.release,
      leanOptions := #[],
      moreLeanArgs := #[],
      weakLeanArgs := #[],
      moreLeancArgs := #[],
      moreServerOptions := #[],
      weakLeancArgs := #[],
      moreLinkArgs := #[],
      weakLinkArgs := #[],
      backend := Lake.Backend.default,
      platformIndependent := none },
    name := `«example-package»,
    manifestFile := none,
    extraDepTargets := #[],
    precompileModules := false,
    moreServerArgs := #[],
    moreGlobalServerArgs := #[],
    srcDir := FilePath.mk ".",
    buildDir := FilePath.mk ".lake/build",
    leanLibDir := FilePath.mk "lib",
    nativeLibDir := FilePath.mk "lib",
    binDir := FilePath.mk "bin",
    irDir := FilePath.mk "ir",
    releaseRepo? := none,
    releaseRepo := none,
    buildArchive? := none,
    buildArchive := ELIDED,
    preferReleaseBuild := false,
    testDriver := "",
    testDriverArgs := #[],
    lintDriver := "",
    lintDriverArgs := #[],
    version := { toSemVerCore := { major := 0, minor := 0, patch := 0 }, specialDescr := "" },
    versionTags := .satisfies #<fun> default,
    description := "",
    keywords := #[],
    homepage := "",
    license := "",
    licenseFiles := #[FilePath.mk "LICENSE"],
    readmeFile := FilePath.mk "README.md",
    reservoir := true},
  relConfigFile := FilePath.mk "lakefile",
  relManifestFile := FilePath.mk "lake-manifest.json",
  scope := "",
  remoteUrl := "",
  depConfigs := #[],
  leanLibConfigs := {`Sorting ↦
      {toLeanConfig := { buildType := Lake.BuildType.release,
          leanOptions := #[],
          moreLeanArgs := #[],
          weakLeanArgs := #[],
          moreLeancArgs := #[],
          moreServerOptions := #[],
          weakLeancArgs := #[],
          moreLinkArgs := #[],
          weakLinkArgs := #[],
          backend := Lake.Backend.default,
          platformIndependent := none },
        name := `Sorting,
        srcDir := FilePath.mk ".",
        roots := #[`Sorting],
        globs := #[Lake.Glob.one `Sorting],
        libName := "Sorting",
        extraDepTargets := #[],
        precompileModules := false,
        defaultFacets := #[`leanArts],
        nativeFacets := #<fun>},
    },
  leanExeConfigs := {},
  externLibConfigs := {},
  opaqueTargetConfigs := {},
  defaultTargets := #[`Sorting],
  scripts := {},
  defaultScripts := #[],
  postUpdateHooks := #[],
  testDriver := "",
  lintDriver := ""}
```
::::
:::::

## Dependencies

Dependencies are specified in the `require` field array of a package configuration, which specifies both the name and the source of each package.
There are three kinds of sources:
 * {ref "reservoir"}[Reservoir], or an alternative package registry
 * Git repositories, which may be local paths or URLs
 * Local paths

::::tomlTableDocs "Requiring Packages" Lake.Dependency skip:=src? skip := opts skip:=subdir skip:=version?

The `path` and `git` fields specify an explicit source for a dependency.
If neither are provided, then the dependency is fetched from {ref "reservoir"}[Reservoir], or an alternative registry if one has been configured.

:::tomlField Lake.Dependency path "Path" System.FilePath
A dependency on the local filesystem, specified by its path.
:::

:::tomlField Lake.Dependency git "Git specification" Lake.DependencySrc
A dependency in a Git repository, specified either by its URL as a string or by a table with the keys:
 * `url`: the repository URL
 * `subDir`: the subdirectory of the Git repository that contains the package's source code
:::

:::tomlField Lake.Dependency rev "Git revision" String
For Git or Reservoir dependencies, this field specifies the Git revision, which may be a branch name, a tag name, or a specific hash.
On Reservoir, the `version` field takes precedence over this field.
:::

:::tomlField Lake.Dependency source "Package Source" Lake.DependencySrc
A dependency source, specified as a self-contained table, which is used when neither the `git` nor the `path` key is present.
The key `type` should be either the string `"git"` or the string `"path"`.
If the type is `"path"`, then there must be a further key `"path"` whose value is a string that provides the location of the package on disk.
If the type is `"git"`, then the following keys should be present:
 * `url`: the repository URL
 * `rev`: the Git revision, which may be a branch name, a tag name, or a specific hash (optional)
 * `subDir`: the subdirectory of the Git repository that contains the package's source code
:::

:::tomlField Lake.Dependency version "version as string" String

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
```
```expected
#[{name := `example, scope := "", version := (some 2.12), src? := none, opts := {} }]
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
    version := (some 2.12),
    src? := some (Lake.DependencySrc.git "https://git.example.com/example.git" (some "main") none),
    opts := {}
  }]
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
    version := none,
    src? := some (Lake.DependencySrc.git "https://git.example.com/example.git" (some "v2.12") none),
    opts := {}
  }]
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
```
```expected
#[{name := `example, scope := "", version := (some git#v2.12), src? := none, opts := {} }]
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
    version := none,
    src? := some (Lake.DependencySrc.path (FilePath.mk "../example")),
    opts := {}
  }]
```
::::
Dependencies on local paths are useful when developing multiple packages in a single repository, or when testing whether a change to a dependency fixes a bug in a downstream package.
:::::

:::::example "Sources as Tables"
The information about the package source can be written in an explicit table:
::::lakeToml Lake.Dependency require
```toml
[[require]]
name = "example"
source = {type = "git", url = "https://git.example.com/example.git"}
```
```expected
#[{name := `example,
    scope := "",
    version := none,
    src? := some (Lake.DependencySrc.git "https://git.example.com/example.git" none none),
    opts := {}
  }]
```
::::
:::::

## Library Targets

Library targets are expected in the `lean_lib` array of tables.

::::tomlTableDocs "Library Targets" Lake.LeanLibConfig skip := backend skip:=globs skip:=nativeFacets
::::

:::::example "Minimal Library Target"
This library declaration supplies only a name:
::::lakeToml Lake.LeanLibConfig lean_lib
```toml
[[lean_lib]]
name = "TacticTools"
```
```expected
#[{toLeanConfig := { buildType := Lake.BuildType.release,
      leanOptions := #[],
      moreLeanArgs := #[],
      weakLeanArgs := #[],
      moreLeancArgs := #[],
      moreServerOptions := #[],
      weakLeancArgs := #[],
      moreLinkArgs := #[],
      weakLinkArgs := #[],
      backend := Lake.Backend.default,
      platformIndependent := none },
    name := `TacticTools,
    srcDir := FilePath.mk ".",
    roots := #[`TacticTools],
    globs := #[Lake.Glob.one `TacticTools],
    libName := "TacticTools",
    extraDepTargets := #[],
    precompileModules := false,
    defaultFacets := #[`leanArts],
    nativeFacets := #<fun>}]
```
::::
The library's source is located in the package's default source directory, in the module hierarchy rooted at `TacticTools`.
:::::

:::::example "Library Target"
This library declaration supplies more options:
::::lakeToml Lake.LeanLibConfig lean_lib
```toml
[[lean_lib]]
name = "TacticTools"
precompileModules = true
srcDir = "src"
```
```expected
#[{toLeanConfig := { buildType := Lake.BuildType.release,
      leanOptions := #[],
      moreLeanArgs := #[],
      weakLeanArgs := #[],
      moreLeancArgs := #[],
      moreServerOptions := #[],
      weakLeancArgs := #[],
      moreLinkArgs := #[],
      weakLinkArgs := #[],
      backend := Lake.Backend.default,
      platformIndependent := none },
    name := `TacticTools,
    srcDir := FilePath.mk "src",
    roots := #[`TacticTools],
    globs := #[Lake.Glob.one `TacticTools],
    libName := "TacticTools",
    extraDepTargets := #[],
    precompileModules := true,
    defaultFacets := #[`leanArts],
    nativeFacets := #<fun>}]
```
::::
The library's source is located in the directory `src`, in the module hierarchy rooted at `TacticTools`.
If its modules are accessed at elaboration time, they will be compiled to native code and linked in, rather than run in the interpreter.
:::::

## Executable Targets

:::: tomlTableDocs "Executable Targets" Lake.LeanExeConfig skip := backend skip:=globs skip:=nativeFacets

::::

:::::example "A Minimal Executable Target"
This executable declaration supplies only a name:
::::lakeToml Lake.LeanExeConfig lean_exe
```toml
[[lean_exe]]
name = "trustworthytool"
```
```expected
#[{toLeanConfig := { buildType := Lake.BuildType.release,
      leanOptions := #[],
      moreLeanArgs := #[],
      weakLeanArgs := #[],
      moreLeancArgs := #[],
      moreServerOptions := #[],
      weakLeancArgs := #[],
      moreLinkArgs := #[],
      weakLinkArgs := #[],
      backend := Lake.Backend.default,
      platformIndependent := none },
    name := `trustworthytool,
    srcDir := FilePath.mk ".",
    root := `trustworthytool,
    exeName := "trustworthytool",
    extraDepTargets := #[],
    supportInterpreter := false,
    nativeFacets := #<fun>}]
```
::::

```lean (show := false)
def main : List String → IO UInt32 := fun _ => pure 0
```

The executable's {lean}`main` function is expected in a module named `trustworthytool.lean` in the package's default source file path.
The resulting executable is named `trustworthytool`.
:::::

:::::example "An Executable Target"
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
#[{toLeanConfig := { buildType := Lake.BuildType.release,
      leanOptions := #[],
      moreLeanArgs := #[],
      weakLeanArgs := #[],
      moreLeancArgs := #[],
      moreServerOptions := #[],
      weakLeancArgs := #[],
      moreLinkArgs := #[],
      weakLinkArgs := #[],
      backend := Lake.Backend.default,
      platformIndependent := none },
    name := `«trustworthy-tool»,
    srcDir := FilePath.mk ".",
    root := `TrustworthyTool,
    exeName := "tt",
    extraDepTargets := #[],
    supportInterpreter := false,
    nativeFacets := #<fun>}]
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


```lean (show := false)
section
open Lake.DSL
```

:::TODO

Concepts

When elaborated

Which features need this?

:::

## Dependencies

:::syntax command
```grammar
$[$doc?:docComment]?
require $spec
```
:::

:::syntax depSpec
```grammar
$name:depName $[@ $[git]? $_:term]? $[$_:fromClause]? $[with $_:term]?
```
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

## Packages
::::syntax command
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
  $[$_:declField $[,]?]*
}
$[where
  $[$_:letRecDecl];*]?
```

There can only be one {keywordOf Lake.DSL.packageDecl}`package` declaration per Lake configuration file.
The defined package configuration will be available for reference as `_package`.

::::

::::syntax command
```grammar
post_update $[$name]? $v
```

{includeDocstring Lake.DSL.postUpdateDecl}

::::

## Targets

:::syntax attr
```grammar
default_target
```
Marks a target as a default.
:::

### Libraries
:::syntax command

```grammar
$[$_:docComment]? $[$_:attributes]?
lean_lib $_:identOrStr
```


```grammar
$[$_:docComment]? $[$_:attributes]?
lean_lib $_:identOrStr where
  $field*
```


```grammar
$[$_:docComment]? $[$_:attributes]?
lean_lib $_:identOrStr {
  $[$_:declField $[,]?]*
}
$[where
  $[$_:letRecDecl];*]?
```
:::

{docstring Lake.LeanLibConfig}

### Executables

:::syntax command

```grammar
$[$_:docComment]? $[$_:attributes]?
lean_exe $_:identOrStr
```


```grammar
$[$_:docComment]? $[$_:attributes]?
lean_exe $_:identOrStr where
  $field*
```


```grammar
$[$_:docComment]? $[$_:attributes]?
lean_exe $_:identOrStr {
  $[$_:declField $[,]?]*
}
$[where
  $[$_:letRecDecl];*]?
```
:::

{docstring Lake.LeanExeConfig}

### External Libraries

:::syntax command

```grammar
$[$_:docComment]? $[$_:attributes]?
extern_lib $_:identOrStr $_? := $_:term
$[where $_*]?
```

{includeDocstring Lake.DSL.externLibDecl}

:::

### Custom Targets

:::syntax command

```grammar
$[$_:docComment]? $[$_:attributes]?
target $_:identOrStr $_? : $ty:term := $_:term
$[where $_*]?
```

{includeDocstring Lake.DSL.externLibDecl}

:::

### Custom Facets

:::syntax command
```grammar
$[$_:docComment]? $[$_:attributes]?
package_facet $_:identOrStr $_? : $ty:term := $_:term
$[where $_*]?
```

{includeDocstring Lake.DSL.packageFacetDecl}

:::

:::syntax command
```grammar
$[$_:docComment]? $[$_:attributes]?
library_facet $_:identOrStr $_? : $ty:term := $_:term
$[where $_*]?
```

{includeDocstring Lake.DSL.libraryFacetDecl}

:::

:::syntax command
```grammar
$[$_:docComment]? $[$_:attributes]?
module_facet $_:identOrStr $_? : $ty:term := $_:term
$[where $_*]?
```

{includeDocstring Lake.DSL.moduleFacetDecl}

:::

## Scripts

:::syntax command
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

:::syntax attr
```grammar
default_script
```

Marks a {tech}[Lake script] as the {tech}[package]'s default.

:::

## Utilities

:::syntax term
```grammar
__dir__
```

{includeDocstring Lake.DSL.dirConst}

:::

:::syntax term
```grammar
get_config? $t
```

{includeDocstring Lake.DSL.getConfig}

:::

:::syntax command

```grammar
meta if $_ then
  $_
$[else $_]?
```

{includeDocstring Lake.DSL.metaIf}

:::

:::syntax cmdDo

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

:::syntax term
```grammar
run_io $t
```

{includeDocstring Lake.DSL.runIO}

:::
