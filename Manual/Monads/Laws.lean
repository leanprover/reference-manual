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
axiom g : α → β
axiom h : β → γ

```

Having {name Functor.map}`map`, {name Pure.pure}`pure`, {name Seq.seq}`seq`, and {name Bind.bind}`bind` operators with the appropriate types is not really enough to make a type constructor into a functor, applicative functor, or monad.
These operators must additionally satisfy certain axioms, which are often called the {deftech}_functor laws_.

For a functor, the {name Functor.map}`map` operation must preserve identity and function composition. In other words, given a purported {name}`Functor` {lean}`f`, for all {lean}`x`​` : `​{lean}`f α`:
 * {lean}`id <$> x = x`, and
 * for all function {lean}`g` and {lean}`h`, {lean}`(h ∘ g) <$> x = h <$> g <$> x`.
Instances that violate these assumptions can be very surprising!

The Lean standard library does not require profs of these properties in every instance of {name}`Functor`.
Nonetheless, if an instance violates them, then it should be considered a bug.
When proofs of these properties are necessary, an instance implicit parameter of type {lean}`LawfulFunctor f` can be used.
The {name}`LawfulFunctor` class includes the necessary proofs.

{docstring LawfulFunctor}

```lean (show := false)
end F
```
:::

```lean (show := false)
section A
axiom g : f (α → β)
axiom g' : α → β
axiom h : f (β → γ)
axiom y : α
variable [Applicative f]
```


Applicative functors {lean}`f` must satisfy four laws:

: Identity

  Applying the identity function through {lean}`f` should be equivalent to not applying it at all.
  This means that {lean}`pure id <*> x = x`.

: Composition

  Composing two functions through {lean}`f` should be equivalent to sequentially applying them through {lean}`f`.
  This means that {lean}`pure (·∘·) <*> h <*> g <*> x = h <*> (g <*> x)`.

: Homomorphism

  Applying a pure function {lean}`g'` to a pure value {lean}`y` through {lean}`f` should be equivalent to applying the function purely outside of {lean}`f`.
  This means that {lean}`pure g' <*> pure y = (pure (g' y) : f β)`.

: Interchange

  Function application through {lean}`f` is equivalent on the left or right of {name Seq.seq}`seq`.
  This means that {lean}`g <*> pure y = pure (· y) <*> g`.


{docstring LawfulApplicative}

Monads

{docstring LawfulMonad}

{docstring LawfulMonad.mk'}

```lean (show := false)
end A
end Laws
```
