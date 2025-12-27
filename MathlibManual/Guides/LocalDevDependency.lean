/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jon Eugster
-/

import VersoManual
import Manual.Meta
import Mathlib

open Lake
open Verso.Genre Manual

set_option pp.rawOnError true
set_option linter.unusedVariables false

set_option maxHeartbeats 0
set_option maxRecDepth 100000000000000000

open Lean.Elab.Tactic

#doc (Manual) "Using local dev version of a dependency" =>

(written by Jon Eugster)

*This tip should be considered a workaround, some care is adviced when trying this non-standard setup!*

*Note:* Things here might change as `lake` is being developed, as features described here are not necessarily officially supported by `lake`. This file has been written for Lean `v4.16.0`. If in doubt, ask for help on [Zulip](https://leanprover.zulipchat.com).

In rare circumstances you might want to use a local copy of a dependency (e.g. `mathlib`) when developing, i.e. to test changes immediately.

You could do this by using a local dependency while developing

```
require mathlib from ".." / "mathlib4"
```

and then change it back to the remote dependency before pushing changes:

```
require "leanprover-community" / "mathlib"
```

However, if you want to do this frequently, here might be a better setup. With the suggested modifications to the `lakefile.lean` below, you get the following behaviour:

* To use the local dependency, call
  ```
  lake update -R -Kmathlib.useDev mathlib
  ```
* To switch back to the remote dependency, call
  ```
  lake update -R mathlib
  ```
* Anybody `require`-ing your project as dependency in there own project will automatically get the remote version of the dependencies.

(*Note:* make sure to read the chapter above about specifying versions when using `lake update`).

For this you need to replace `require "leanprover-community" / "mathlib"` in your `lakefile.lean` with the following instructions:

```
open Lake DSL

/-- The local dependency. Using a relative path. -/
def LocalMathlib : Dependency where
  name := `mathlib
  src? := some <| .path (".." / "mathlib4")
  scope := ""
  version? := none
  opts := {}

/--
The remote dependency. Note that "master" is the tag/branch
you want to clone from.
-/
def RemoteMathlib : Dependency where
  name := `mathlib
  /-
  You can also write `src? := none` to get the package
  from Reservoir instead (if `scope` is specified
  correctly), or you can replace `"master"` with
  `none` to not specify the input branch/tag.
  -/
  src? := some <| .git
    "https://github.com/leanprover-community/mathlib4.git"
    "master" none
  scope := "leanprover-community"
  version? := none
  opts := {}


/-
Choose `mathlib` dependency locally if
`-Kmathlib.useDev` is provided.
-/
open Lean in
#eval (do
  let depName :=
    if get_config? mathlib.useDev |>.isSome then
      ``LocalMathlib else ``RemoteMathlib
  modifyEnv (fun env =>
    Lake.packageDepAttr.ext.addEntry env depName)
  : Elab.Command.CommandElabM Unit)
```
