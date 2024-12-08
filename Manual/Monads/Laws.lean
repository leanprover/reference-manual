/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "Laws" =>

```lean (show := false)
section Laws
universe u u' v
axiom f : Type u → Type v
axiom m : Type u → Type v
variable [Functor f]
variable [Applicative f]
variable [Monad m]
axiom α : Type u'
axiom β : Type u'
axiom γ : Type u'
axiom x : f α
```

:::keepEnv
```lean (show := false)
section F
variable {f : Type u → Type v} [Functor f] {α β : Type u} {g : α → β} {h : β → γ} {x : f α}
```

Having {name Functor.map}`map`, {name Pure.pure}`pure`, {name Seq.seq}`seq`, and {name Bind.bind}`bind` operators with the appropriate types is not really sufficient to have a functor, applicative functor, or monad.
These operators must additionally satisfy certain axioms, which are often called the {deftech}_laws_ of the type class.

For a functor, the {name Functor.map}`map` operation must preserve identity and function composition. In other words, given a purported {name}`Functor` {lean}`f`, for all {lean}`x`​` : `​{lean}`f α`:
 * {lean}`id <$> x = x`, and
 * for all function {lean}`g` and {lean}`h`, {lean}`(h ∘ g) <$> x = h <$> g <$> x`.
Instances that violate these assumptions can be very surprising!
Additionally, because {lean}`Functor` includes {name Functor.mapConst}`mapConst` to enable instances to provide a more efficient implementation, a lawful functor's {name Functor.mapConst}`mapConst` should be equivalent to its default implementation.

The Lean standard library does not require profs of these properties in every instance of {name}`Functor`.
Nonetheless, if an instance violates them, then it should be considered a bug.
When proofs of these properties are necessary, an instance implicit parameter of type {lean}`LawfulFunctor f` can be used.
The {name}`LawfulFunctor` class includes the necessary proofs.

{docstring LawfulFunctor}

```lean (show := false)
end F
```
:::




In addition to proving that the potentially-optimized {name}`SeqLeft.seqLeft` and {name}`SeqRight.seqRight` operations are equivalent to their default implementations, Applicative functors {lean}`f` must satisfy four laws.

{docstring LawfulApplicative}

The {deftech}[monad laws] specify that {name}`pure` followed by {name}`bind` should be equivalent to function application (that is, {name}`pure` has no effects), that {name}`bind` followed by {name}`pure` around a function application is equivalent to {name Functor.map}`map`, and that {name}`bind` is associative.

{docstring LawfulMonad}

{docstring LawfulMonad.mk'}
