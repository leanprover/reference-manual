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

#doc (Manual) "Scripts" =>
%%%
tag := "lake-scripts"
%%%

Lake {tech}[package configuration] files may include {deftech}_Lake scripts_, which are embedded programs that can be executed from the command line.
Scripts are intended to be used for project-specific tasks that are not already well-served by Lake's other features.
While ordinary executable programs are run in the {name}`IO` {tech}[monad], scripts are run in {name Lake.ScriptM}`ScriptM`, which extends {name}`IO` with information about the workspace.
Because they are Lean definitions, Lake scripts can only be defined in the Lean configuration format.

:::::TODO

Restore the following once we can import enough of Lake to elaborate it

````
```lean -show
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

```lean -show
end
```
````

:::::
