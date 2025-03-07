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

#doc (Manual) "Follow Stable Dependencies" =>

(written by Jon Eugster)

*This tip should be considered a workaround, some care is adviced when trying this non-standard setup!*

*Note:* Things here might change as `lake` is being developed, as features described here are not necessarily officially supported by `lake`. This file has been written for Lean `v4.16.0`. If in doubt, ask for help on [Zulip](https://leanprover.zulipchat.com).

If your Lean project only wants to following the stable releases of dependencies (i.e. `v4.16.0`, `v4.17.0`, etc.) you could do the following trick:

In your `lakefile.lean`, add

```lean
def leanVersion : String := s!"v{Lean.versionString}"
```

and then suffix all `require`s with `@ leanVersion`:

```
require "leanprover-community" / "mathlib" @ leanVersion
```

*Note:* for this to work, the repository of each dependency needs to have a tag (or branch) for the Lean version you're using, e.g. look at [the mathlib tags](https://github.com/leanprover-community/mathlib4/tags).

If you specified the version for all dependencies in your project, you can then update your project simply by

* Edit `lean-toolchain` to have the new toolchain `leanprover/lean4:v4.17.0`.
* Call `lake update -R`.

*Note:* a blank `lake update -R` is only reasonable if *all* required dependencies in your project have a version specified with `@`.
