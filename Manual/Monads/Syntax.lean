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

#doc (Manual) "Syntax" =>


# Infix Operators

:::syntax term
```grammar
$_ >>= $_
```
```grammar
$_ =<< $_
```

```grammar
$_ >=> $_
```
```grammar
$_ <=< $_
```

```grammar
$_ <$> $_
```

```grammar
$_ <&> $_
```

```grammar
$_ <*> $_
```

```grammar
$_ *> $_
```

```grammar
$_ <* $_
```

:::

# `do`-Notation
%%%
tag := "do-notation"
%%%

Monads are primarily used via {keywordOf Lean.Parser.Term.do}`do`-notation, which is an embedded language for programming in an imperative style.
It provides familiar syntax for sequencing effectful operations, early return, local mutable variables, loops, and exception handling.
All of these features are translated to the operations of the {lean}`Monad` type class, with a few of them requiring addition instances of classes such as {lean}`ForIn` that specify iteration over containers.
A {keywordOf Lean.Parser.Term.do}`do` term consists of the keyword {keywordOf Lean.Parser.Term.do}`do` followed by a sequence of {deftech}_{keywordOf Lean.Parser.Term.do}`do` items_.

:::syntax term
```grammar
do $stmt*
```
The items in a {keywordOf Lean.Parser.Term.do}`do` may be separated by semicolons; otherwise, each should be on its own line and they should have equal indentation.
:::

```lean (show := false)
section
variable {m : Type → Type} [Monad m] {α β γ: Type} {e1 : m Unit} {e : β} {es : m α}
```

## Sequential Computations

One form of {tech}[{keywordOf Lean.Parser.Term.do}`do` item] is a term.

:::syntax Lean.Parser.Term.doSeqItem
```grammar
$e:term
```
:::


A term followed by a sequence of items is translated to a use {name}`bind`; in particular, {lean}`do e1; es` is translated to {lean}`e1 >>= fun () => do es`.
The result of the term's computation may also be named, allowing it to be used in subsequent steps:

```lean (show := false)
section
variable {e1 : m β} {e1? : m (Option β)} {fallback : m α} {e2 : m γ} {f : β → γ → m Unit} {g : γ → α} {h : β → m γ}
```

:::syntax Lean.Parser.Term.doSeqItem
There are two forms of monadic {keywordOf Lean.Parser.Term.doLet}`let`-binding in a {keywordOf Lean.Parser.Term.do}`do` block.
The first binds an identifier to the result, with an optional type annotation:
```grammar
let $x:ident$[:$e]? ← $e:term
```
The second binds a pattern to the result.
The fallback clause, beginning with `|`, specifies the behavior when the pattern does not match the result.
```grammar
let $x:term ← $e:term
  $[| $e]?
```
:::
This syntax is also translated to a use of {name}`bind`.
{lean}`do let x ← e1; es` is translated to {lean}`e1 >>= fun x => do es`.

:::TODO
Translation of fallback (it requires inline-block display-mode elaborated terms)
:::


{keywordOf Lean.Parser.Term.doLet}`let` may also be used with the standard definition syntax `:=` instead of `←`.
This indicates a pure, rather than monadic, definition:
:::syntax Lean.Parser.Term.doSeqItem
```grammar
let v := $e:term
```
:::
{lean}`do let x := e; es` is translated to {lean}`let x := e; do es`.

Within a {keywordOf Lean.Parser.Term.do}`do` block, `←` may be used as a prefix operator.
The expression to which it is applied is replaced with a fresh variable, which is bound using {name}`bind` just before the current step.
This allows monadic effects to be used in positions that otherwise might expect a pure value, while still maintaining the distinction between _describing_ an effectful computation and actually _executing_ its effects.
Multiple occurrences of `←` are processed from left to right, inside to outside.

Under these rules, {lean}`do f (← e1) (← e2); es` is translated to {lean}`do let x ← e1; let y ← e2; f x y; es`, and {lean}`do let x := g (← h (← e1)); es` is translated to {lean}`do let y ← e1; let z ← h y; let x := g z; es`.

## Early Return

:::syntax Lean.Parser.Term.doSeqItem
```grammar
return $e
```

```grammar
return
```
:::

Not all monads include early return.
Thus, when a {keywordOf Lean.Parser.Term.do}`do` block contains {keywordOf Lean.Parser.Term.doReturn}`return`, the code needs to be rewritten to simulate the effect.
A program that uses early return to compute a value of type {lean}`α` in a monad {lean}`m` can be thought of as a program in the monad {lean}`ExceptT α m α`: early-returned values take the exception pathway, while ordinary returns do not.
Then, an outer handler can return the value from either code paths.
Internally, the {keywordOf Lean.Parser.Term.do}`do` elaborator performs a translation very much like this one.

On its own, {keywordOf Lean.Parser.Term.doReturn}`return` is short for {keywordOf Lean.Parser.Term.doReturn}`return`​` `​{lean}`()`.

## Local Mutable State

Local mutable state is mutable state that cannot escape the {keywordOf Lean.Parser.Term.do}`do` block in which it is defined.
The {keywordOf Lean.Parser.Term.doLet}`let mut` binder introduces a locally-mutable binding.
:::syntax Lean.Parser.Term.doSeqItem
Mutable bindings may be initialized either with pure computations or with monadic computations:
```grammar
let mut $x := $e
```
```grammar
let mut $x ← $e
```

Similarly, they can be mutated either with pure values or the results of monad computations:
```grammar (of := Lean.Parser.Term.doReassign)
$x:ident$[: $_]?  := $e:term
```
```grammar (of := Lean.Parser.Term.doReassign)
$x:term$[: $_]? := $e:term
```
```grammar (of := Lean.Parser.Term.doReassignArrow)
$x:ident$[: $_]? ← $e:term
```
```grammar (of := Lean.Parser.Term.doReassignArrow)
$x:term ← $e:term
  $[| $e]?
```

:::

These locally-mutable bindings are less powerful than a {tech}[state monad] because they are not mutable outside their lexical scope; this also makes them easier to reason about.
When {keywordOf Lean.Parser.Term.do}`do` blocks contain mutable bindings, the {keywordOf Lean.Parser.Term.do}`do` elaborator transforms the expression similarly to the way that {lean}`StateT` would, constructing a new monad and initializing it with the correct values.

## Control Structures

There are {keywordOf Lean.Parser.Term.do}`do` items that correspond to most of Lean's term-level control structures.
When they occur as a step in a {keywordOf Lean.Parser.Term.do}`do` block, they are interpreted as {keywordOf Lean.Parser.Term.do}`do` items rather than terms.
Each branch of the control structures is a sequence of {keywordOf Lean.Parser.Term.do}`do` items, rather than a term, and some of them are more syntactically flexible than their corresponding terms.

:::syntax Lean.Parser.Term.doSeqItem
```grammar
if $[$h :]? $e then
  $e*
$[else
  $_*]?
```
:::

:::syntax Lean.Parser.Term.doSeqItem
```grammar
match $[$[$h :]? $e],* with
  $[| $t,* => $e*]*
```
:::


:::syntax Lean.Parser.Term.doSeqItem
```grammar
unless $e do
  $e*
```
:::

## Iteration

:::syntax Lean.Parser.Term.doSeqItem
```grammar
for $[$[$h :]? $x in $y],* do
  $e*
```
:::

:::syntax Lean.Parser.Term.doSeqItem
```grammar
while $e do
  $e*
```
```grammar
while $h : $e do
  $e*
```
:::

:::syntax Lean.Parser.Term.doSeqItem
```grammar
repeat
  $e*
```
:::

:::syntax Lean.Parser.Term.doSeqItem
```grammar
continue
```
```grammar
break
```
:::



```lean (show := false)
end
```

```lean (show := false)
-- tests for this section
set_option pp.all true

/--
info: @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) Unit α e1 fun (x : PUnit.{1}) => es : m α
-/
#guard_msgs in
#check do e1; es

section
variable {e1 : m β}
/-- info: @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) β α e1 fun (x : β) => es : m α -/
#guard_msgs in
#check do let x ← e1; es
end

/--
info: let x : β := e;
es : m α
-/
#guard_msgs in
#check do let x := e; es

variable {e1 : m β} {e2 : m γ} {f : β → γ → m Unit} {g : γ → α} {h : β → m γ}

/--
info: @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) β α e1 fun (__do_lift : β) =>
  @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) γ α e2 fun (__do_lift_1 : γ) =>
    @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) Unit α (f __do_lift __do_lift_1) fun (x : PUnit.{1}) => es : m α
-/
#guard_msgs in
#check do f (← e1) (← e2); es

/--
info: @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) β α e1 fun (__do_lift : β) =>
  @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) γ α (h __do_lift) fun (__do_lift : γ) =>
    let x : α := g __do_lift;
    es : m α
-/
#guard_msgs in
#check do let x := g (← h (← e1)); es

end


```

# Iteration

{docstring ForIn}

{docstring ForIn'}

{docstring ForM}

{docstring ForM.forIn}
