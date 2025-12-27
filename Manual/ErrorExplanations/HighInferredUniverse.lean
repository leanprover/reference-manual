/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rob Simmons, Kyle Miller
-/

import VersoManual
import Manual.Meta.ErrorExplanation

open Lean
open Verso.Genre Manual InlineLean

#doc (Manual) "About: `highInferredUniverse`" =>
%%%
shortTitle := "highInferredUniverse"
%%%

{errorExplanationHeader lean.highInferredUniverse}

This error message appears when Lean's elaboration algorithm is about to assign a new type to a
higher universe than may be necessary.

::::paragraph
Constructor argument universe levels must be no greater than the resulting universe level, so given
this definition:
:::keepEnv
```lean
inductive MaybeTwo (α : Type u)
  | none
  | some (fst snd : α)
```
```lean -show
variable (α : Type u)
```
Lean must classify {lean}`MaybeTwo α` as a {lean}`Type u`, or, equivalently, as a
{lean}`Sort (u + 1)`. (See the reference guide to {ref "universes-sorts"}[Universes] for more
details on the relationship between {lean}`Prop`, {lean}`Sort`, and {lean}`Type`.)
:::
::::

Lean chooses to avoid silently assigning a new type to a universe that might cause confusion later.
This error often indicates that the universe annotations need to be in a slightly different form,
or that more specific annotations are required.

# Examples
:::errorExample "Use of `Type` May Force Universe Too High"
```broken
structure MyPair (α β : Sort u) : Type _ where
  (a : α)
  (b : β)
```

```output
Resulting type is of the form
  Type ?u.6
but the universes of constructor arguments suggest that this could accidentally be a higher universe than necessary. Explicitly providing a resulting type will silence this error. Universe inference suggests using
  Sort (max 1 u)
if the resulting universe level should be at the above universe level or higher.

Explanation: At this point in elaboration, universe level unification has committed to using a resulting universe level of the form `?u.6+1`. Constructor argument universe levels must be no greater than the resulting universe level, and this condition implies the following constraint(s):
  u ≤ ?u.6+1
However, such constraint(s) usually indicate that the resulting universe level should have been in a different form. For example, if the resulting type is of the form `Sort (_ + 1)` and a constructor argument is in universe `Sort u`, then universe inference would yield `Sort (u + 1)`, but the resulting type `Sort (max 1 u)` would avoid being in a higher universe than necessary.
```

```fixed "remove annotation"
structure MyPair (α β : Sort u) where
  (a : α)
  (b : β)
```

```fixed "accept suggestion"
structure MyPair (α β : Sort u) : Sort (max 1 u) where
  (a : α)
  (b : β)
```

```fixed "restrict arguments"
structure MyPair (α β : Type u) : Type _ where
  (a : α)
  (b : β)
```

```fixed "make large type explicit"
structure MyPair (α β : Sort u) : Type u where
  (a : α)
  (b : β)
```

```lean -show
variable (α : Type u)
```

The initial type annotation {lean}`Type _` forces `MyPair` into a universe that looks like
{lean}`Sort (_ + 1)`, but the best universe for `MyPair` is {lean}`Sort (max u 1)`. (See the section
on {ref "prop-vs-type"}[Prop vs Type] for why it is {lean}`Sort (max u 1)` and not just
{lean}`Sort u`.)

The first two fixes are all equivalent, and allow `MyPair` to have any non-zero universe that
is larger than `u`. The last two fixes make `MyPair` less general, but also silence the error.
:::

:::errorExample "Inductive Definition Needs Sort Annotations"
```broken
inductive Bar
| foobar {Foo} : Foo → Bar
| barbar : Option Bar → Bar
```
```output
Resulting type is of the form
  Type ?u.16
but the universes of constructor arguments suggest that this could accidentally be a higher universe than necessary. Explicitly providing a resulting type will silence this error. Universe inference suggests using
  Type u_1
if the resulting universe level should be at the above universe level or higher.

Explanation: At this point in elaboration, universe level unification has committed to using a resulting universe level of the form `?u.16+1`. Constructor argument universe levels must be no greater than the resulting universe level, and this condition implies the following constraint(s):
  u_1 ≤ ?u.16+1
However, such constraint(s) usually indicate that the resulting universe level should have been in a different form. For example, if the resulting type is of the form `Sort (_ + 1)` and a constructor argument is in universe `Sort u`, then universe inference would yield `Sort (u + 1)`, but the resulting type `Sort (max 1 u)` would avoid being in a higher universe than necessary.
```
```fixed
inductive Bar : Type u
| foobar {Foo : Sort u} : Foo → Bar
| barbar : Option Bar → Bar
```

In this case, the error message is a false positive, but the issue can be easily fixed with
clarifying annotations. After annotating Foo with a universe `u`, the overall type can be assigned
type that the error message suggests, which silences the error.
:::
