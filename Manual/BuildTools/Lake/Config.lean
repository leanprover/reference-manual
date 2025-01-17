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


open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "Configuration File Format" =>
%%%
tag := "lake-config"
%%%

# Declarative TOML Format

TOML{margin}[[_Tom's Obvious Minimal Language_](https://toml.io/en/) is a standardized format for configuration files.] configuration files describe the most-used, declarative subset of Lake {tech}[package configuration] files.
TOML files denote _tables_, which map keys to values.
Values may consist of strings, numbers, arrays of values, or further tables.
Because TOML allows considerable flexibility in file structure, this reference documents the values that are expected rather than the specific syntax used to produce them.

The contents of `lakefile.toml` should denote a TOML table that describes a Lean package.
This configuration consists of both scalar fields that describe the entire package, as well as the following fields that contain arrays of further tables:
 * `require`
 * `lean_lib`
 * `lean_exe`
 * `defaultTargets`


## Package Configuration

{tomlTableDocs "Package Configuration" Lake.PackageConfig skip:=backend}

:::tomlField Lake.PackageConfig defaultTargets "default targets' names (array)" String

{includeDocstring Lake.Package.defaultTargets}

:::


## Dependencies

{tomlTableDocs "Dependencies" Lake.Dependency skip:=src? skip := opts skip:=subdir skip:=version? }

:::tomlField Lake.Dependency path "Path" System.FilePath
A dependency on the local filesystem, specified by its path.
:::

:::tomlField Lake.Dependency git "Git specification" Lake.DependencySrc
A dependency in a Git repository, specified either by its URL as a string or by a table with the keys:
 * `url`: the repository URL
 * `subDir`: the subdirectory of the Git repository that contains the package's source code
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

## Library Targets

{tomlTableDocs "Library Targets" Lake.LeanLibConfig skip := backend skip:=globs skip:=nativeFacets}

## Executable Targets

{tomlTableDocs "Executable Targets" Lake.LeanExeConfig skip := backend skip:=globs skip:=nativeFacets}



# Lean Format
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
