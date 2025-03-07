/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jon Eugster
-/

import VersoManual
import Manual.Meta
import Mathlib

open Verso.Genre Manual

set_option pp.rawOnError true
set_option linter.unusedVariables false

set_option maxHeartbeats 0
set_option maxRecDepth 100000000000000000

open Lean.Elab.Tactic

#doc (Manual) "Shared Mathlib Installation" =>

(written by Jon Eugster)

*This tip should be considered a workaround, some care is adviced when trying this non-standard setup!*

*Note:* Things here might change as `lake` is being developed, as features described here are not necessarily officially supported by `lake`. This file has been written for Lean `v4.16.0`. If in doubt, ask for help on [Zulip](https://leanprover.zulipchat.com).

If you start many projects which all use the latest stable version of mathlib
by default each project will download its own clone.
If you, for example, have little disk space available,
it might be worth setting them up using one centralised copy of mathlib instead.

*Note*: This means additional effort when upgrading the mathlib version,
as you need to update all your projects at once.

*Note*: Whenever this tutorial mentions the `lakefile.lean`, you should make the mentioned
modifications to your `lakefile.toml` if you have this instead. Every Lean project
has exactly one of these two configuration files.

*Note*: The VSCode extension does a lot of things automatically and it's hard to account for all of them in this tutorial.
The tutorial is written without use of the extension, so probably best to not press any buttons in VSCode until you followed the steps
here.

Here is the current best practice to achieve this.

1) First, clone a version of mathlib somewhere on your computer:

   ```
   git clone --branch v4.16.0 git@github.com:leanprover-community/mathlib4.git
   ```
   Note that `v4.16.0` is the tag of the latest release, you can look at [mathlib's tags](https://github.com/leanprover-community/mathlib4/tags) to find out which is the most recent release version.

   The above line assumes you have set up git using an SSH key.
   If you have not set this up correctly, you may want to
   use `git clone --branch v4.16.0 https://github.com/leanprover-community/mathlib4.git` instead.

2) Go inside your mathlib and download the current cache:

   ```
   cd mathlib4
   lake exe cache get
   ```

   Additionally, I personally recommend calling

   ```
   chmod -R u-w .lake/build
   ```

   to prevent `lake` from screwing up your mathlib installation. However, make sure you're actually the owner of that folder (or a sudo user)!

3) If you ever want to **update** your global mathlib, come back to the mathlib directory and call
   ```
   # chmod -R u+w .lake/build   # if you removed these right earlier
   git checkout v4.17.0
   lake exe cache get
   # chmod -R u-w .lake/build   # see step above
   ```
   with the [version](https://github.com/leanprover-community/mathlib4/tags) you'd like to update to.
4) If you don't already have a Lean project, create it.
   ```
   cd ..
   lake +leanprover/lean4:v4.16.0 new MyProject math.lean
   cd MyProject
   ```
   *Note*: There seems to be a bug that this still writes a different toolchain to `MyProject/lean-toolchain`, thus look at
   the first point of the next step.
5) In the project `MyProject` you need to modify the following things:
   * Make sure `lean-toolchain` contains the string `leanprover/lean4:v4.16.0` with the same version your shared mathlib is at.
   * In `lakefile.lean`, replace the line `require "leanprover-community" / "mathlib"` with

     ```
     require mathlib from ".." / "relative" / "path" / "to" / "mathlib4"
     ```
   * Now inside `MyProject` you need to clean up lake:

     ```
     MATHLIB_NO_CACHE_ON_UPDATE=1 lake update -R mathlib # use the new path for mathlib
     lake exe cache get # see the bug/feature about duplicated dependencies below
     rm -rf .lake/packages/mathlib # delete the previous local clone of mathlib
     ```

     *Note*: It seems like a bug/feature that all dependencies of Mathlib are duplicated,
     once in `../relative/path/to/mathlib4/.lake/packages` and once in
     `.lake/packages`. Calling `lake exe cache get` seems to add the build files for the copies under `./.lake/packages`

     *Note*: deleting stuff in `.lake`, even `rm -rf .lake`, is a reasonably safe action as it only contains build artifacts that are fully recovered by the next `lake` call.
   * Your project should be ready: Add `import Mathlib` to a file (`MyProject.lean`) and call

     ```
     lake build
     ```

     This should not take very long, and in particular it should *NOT* recompile anything from proofwidgets, batteries, mathlib, etc.
     If it does, your setup failed somehow.
6) When you updated your global mathlib it might be enough to update the `lean-toolchain` of the project to the new version

   ```
   lake update -R mathlib
   ```
   which would in theory update everything automatically. This does the following:

   * mathlib's post-update hook updates the `lean-toolchain` to the one mathlib uses
   * `lake exe cache get` is called to copy the cache of mathlib's dependencies to the (redundant?) copies at `.lake/packages/`

   However, if there are breaking changes to the `lakefile` parsing, you might need to try the following manual steps:

   * edit `lean-toolchain` to be the same as your global mathlib.
   * make sure `lakefile.lean` parses without error in the new version.
   * try `lake update -R mathlib` again.
