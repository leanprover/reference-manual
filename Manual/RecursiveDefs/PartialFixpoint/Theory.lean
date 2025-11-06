/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta
import Manual.Meta.Monotonicity

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

open Lean.Order


#doc (Manual) "Theory and Construction" =>
%%%
tag := "partial-fixpoint-theory"
%%%

The construction builds on a variant of the Knaster–Tarski theorem: In a chain-complete partial order, every monotone function has a least fixed point.

The necessary theory is found in the `Lean.Order` namespace.
This is not meant to be a general purpose library of order theoretic results.
Instead, the definitions and theorems in `Lean.Order` are only intended as implementation details of the {keywordOf Lean.Parser.Command.declaration}`partial_fixpoint` feature, and they should be considered a private API that may change without notice.

The notion of a partial order, and that of a chain-complete partial order, are represented by the type classes {name}`Lean.Order.PartialOrder` and {name}`Lean.Order.CCPO`, respectively.

{docstring Lean.Order.PartialOrder +allowMissing}

{docstring Lean.Order.CCPO +allowMissing}

```lean -show
section
open Lean.Order
variable {α : Type u} {β : Type v} [PartialOrder α] [PartialOrder β] (f : α → β) (x y : α)
```

A function is monotone if it preserves partial orders.
That is, if {lean}`x ⊑ y` then {lean}`f x ⊑ f y`.
The operator `⊑` represent {name}`Lean.Order.PartialOrder.rel`.

{docstring Lean.Order.monotone}

The fixpoint of a monotone function can be taken using {name}`fix`, which indeed constructs a fixpoint, as shown by {name}`fix_eq`,

{docstring Lean.Order.fix}

{docstring Lean.Order.fix_eq}

:::paragraph

To construct the partial fixpoint, Lean first synthesizes a suitable {name}`CCPO` instance.

```lean -show
section
universe u v
variable (α : Type u)
variable (β : α → Sort v) [∀ x, CCPO (β x)]
variable (w : α)
```

* If the function's result type has a dedicated instance, like {name}`Option` has with {name}`instCCPOOption`, this is used together with the instance for the function type, {name}`instCCPOPi`, to construct an instance for the whole function's type.

* Otherwise, if the function's type can be shown to be inhabited by a witness {lean}`w`, then the instance {name}`FlatOrder.instCCPO` for the wrapper type {lean}`FlatOrder w` is used. In this order, {lean}`w` is a least element and all other elements are incomparable.

```lean -show
end
```

:::

Next, the recursive calls in the right-hand side of the function definitions are abstracted; this turns into the argument `f` of {name}`fix`. The monotonicity requirement is solved by the {tactic}`monotonicity` tactic, which applies compositional monotonicity lemmas in a syntax-driven way.

```lean -show
section
set_option linter.unusedVariables false
variable {α : Sort u} {β : Sort v} [PartialOrder α] [PartialOrder β] (more : (x : α) → β) (x : α)

local macro "…" x:term:arg "…" : term => `(more $x)
```

The tactic solves goals of the form {lean}`monotone (fun x => … x …)` using the following steps:

* Applying {name}`monotone_const` when there is no dependency on {lean}`x` left.
* Splitting on {keywordOf Lean.Parser.Term.match}`match` expressions.
* Splitting on {keywordOf termIfThenElse}`if` expressions.
* Moving {keywordOf Lean.Parser.Term.let}`let` expression to the context, if the value and type do not depend on {lean}`x`.
* Zeta-reducing a {keywordOf Lean.Parser.Term.let}`let` expression when value and type do depend on {lean}`x`.
* Applying lemmas annotated with {attr}`partial_fixpoint_monotone`

```lean -show
end
```

The following monotonicity lemmas are registered, and should allow recursive calls under the given higher-order functions in the arguments indicated by `·` (but not the other arguments, shown as `_`).

{monotonicityLemmas}
