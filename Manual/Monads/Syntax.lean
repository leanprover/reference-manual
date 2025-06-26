/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Papers

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option linter.unusedVariables false
-- set_option trace.SubVerso.Highlighting.Code true

set_option guard_msgs.diff true

#doc (Manual) "Syntax" =>

Lean supports programming with functors, applicative functors, and monads via special syntax:
 * Infix operators are provided for the most common operations.
 * An embedded language called {tech}[{keywordOf Lean.Parser.Term.do}`do`-notation] allows the use of imperative syntax when writing programs in a monad.

# Infix Operators

Infix operators are primarily useful in smaller expressions, or when there is no {lean}`Monad` instance.

## Functors

```lean (show := false)
section FOps
variable {f : Type u → Type v} [Functor f] {α β : Type u} {g : α → β} {x : f α}
```
There are two infix operators for {name}`Functor.map`.

:::syntax term (title := "Functor Operators")
{lean}`g <$> x` is short for {lean}`Functor.map g x`.
```grammar
$_ <$> $_
```

{lean}`x <&> g` is short for {lean}`Functor.map g x`.
```grammar
$_ <&> $_
```
:::

```lean (show := false)
example : g <$> x = Functor.map g x := by rfl
example : x <&> g = Functor.map g x := by rfl
end FOps
```

## Applicative Functors

```lean (show := false)
section AOps
variable {f : Type u → Type v} [Applicative f] [Alternative f] {α β : Type u} {g : f (α → β)} {x e1 e e' : f α} {e2 : f β}
```

:::syntax term (title := "Applicative Operators")
{lean}`g <*> x` is short for {lean}`Seq.seq g (fun () => x)`.
The function is inserted to delay evaluation because control might not reach the argument.
```grammar
$_ <*> $_
```

{lean}`e1 *> e2` is short for {lean}`SeqRight.seqRight e1 (fun () => e2)`.
```grammar
$_ *> $_
```

{lean}`e1 <* e2` is short for {lean}`SeqLeft.seqLeft e1 (fun () => e2)`.
```grammar
$_ <* $_
```
:::

Many applicative functors also support failure and recovery via the {name}`Alternative` type class.
This class also has an infix operator.

:::syntax term (title := "Alternative Operators")
{lean}`e <|> e'` is short for {lean}`OrElse.orElse e (fun () => e')`.
The function is inserted to delay evaluation because control might not reach the argument.
```grammar
$_ <|> $_
```
:::


```lean (show := false)
example : g <*> x = Seq.seq g (fun () => x) := by rfl
example : e1 *> e2 = SeqRight.seqRight e1 (fun () => e2) := by rfl
example : e1 <* e2 = SeqLeft.seqLeft e1 (fun () => e2) := by rfl
example : (e <|> e') = (OrElse.orElse e (fun () => e')) := by rfl
end AOps
```

:::::keepEnv
```lean
structure User where
  name : String
  favoriteNat : Nat
def main : IO Unit := pure ()
```
::::example "Infix `Functor` and `Applicative` Operators"
A common functional programming idiom is to use a pure function in some context with effects by applying it via {name}`Functor.map` and {name}`Seq.seq`.
The function is applied to its sequence of arguments using `<$>`, and the arguments are separated by `<*>`.

In this example, the constructor {name}`User.mk` is applied via this idiom in the body of {lean}`main`.
:::ioExample
```ioLean
def getName : IO String := do
  IO.println "What is your name?"
  return (← (← IO.getStdin).getLine).trimRight

partial def getFavoriteNat : IO Nat := do
  IO.println "What is your favorite natural number?"
  let line ← (← IO.getStdin).getLine
  if let some n := line.trim.toNat? then
    return n
  else
    IO.println "Let's try again."
    getFavoriteNat

structure User where
  name : String
  favoriteNat : Nat
deriving Repr

def main : IO Unit := do
  let user ← User.mk <$> getName <*> getFavoriteNat
  IO.println (repr user)
```
When run with this input:
```stdin
A. Lean User
None
42
```
it produces this output:
```stdout
What is your name?
What is your favorite natural number?
Let's try again.
What is your favorite natural number?
{ name := "A. Lean User", favoriteNat := 42 }
```
:::

::::
:::::

## Monads

Monads are primarily used via {tech}[{keywordOf Lean.Parser.Term.do}`do`-notation].
However, it can sometimes be convenient to describe monadic computations via operators.

```lean (show := false)
section MOps
variable {m : Type u → Type v} [Monad m] {α β : Type u} {act : m α} {f : α → m β} {g : β → m γ}
```

:::syntax term (title := "Monad Operators")

{lean}`act >>= f` is syntax for {lean}`Bind.bind act f`.
```grammar
$_ >>= $_
```

Similarly, the reversed operator {lean}`f =<< act` is syntax for {lean}`Bind.bind act f`.
```grammar
$_ =<< $_
```

The Kleisli composition operators {name}`Bind.kleisliRight` and {name}`Bind.kleisliLeft` also have infix operators.
```grammar
$_ >=> $_
```
```grammar
$_ <=< $_
```

:::

```lean (show := false)
example : act >>= f = Bind.bind act f := by rfl
example : f =<< act = Bind.bind act f := rfl
example : f >=> g = Bind.kleisliRight f g := by rfl
example : g <=< f = Bind.kleisliLeft g f := by rfl
end MOps
```


# `do`-Notation
%%%
tag := "do-notation"
%%%

Monads are primarily used via {deftech}[{keywordOf Lean.Parser.Term.do}`do`-notation], which is an embedded language for programming in an imperative style.
It provides familiar syntax for sequencing effectful operations, early return, local mutable variables, loops, and exception handling.
All of these features are translated to the operations of the {lean}`Monad` type class, with a few of them requiring addition instances of classes such as {lean}`ForIn` that specify iteration over containers.
For more details about the design of {keywordOf Lean.Parser.Term.do}`do`-notation, please consult {citet doUnchained}[].
A {keywordOf Lean.Parser.Term.do}`do` term consists of the keyword {keywordOf Lean.Parser.Term.do}`do` followed by a sequence of {deftech}_{keywordOf Lean.Parser.Term.do}`do` items_.

:::syntax term (title := "`do`-Notation")
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

:::syntax Lean.Parser.Term.doSeqItem (title := "Terms in `do`-Notation")
```grammar
$e:term
```
:::


A term followed by a sequence of items is translated to a use of {name}`bind`; in particular, {lean}`do e1; es` is translated to {lean}`e1 >>= fun () => do es`.


:::table (header := true)
*
  * {keywordOf Lean.Parser.Term.do}`do` Item
  * Desugaring
*
  * ```leanTerm
    do
    e1
    es
    ```
  * ```leanTerm
    e1 >>= fun () => do es
    ```
:::

```lean (show := false) (keep := false)
def ex1a := do e1; es
def ex1b := e1 >>= fun () => do es
example : @ex1a = @ex1b := by rfl
```

The result of the term's computation may also be named, allowing it to be used in subsequent steps.
This is done using {keywordOf Lean.Parser.Term.doLet}`let`.

```lean (show := false)
section
variable {e1 : m β} {e1? : m (Option β)} {fallback : m α} {e2 : m γ} {f : β → γ → m Unit} {g : γ → α} {h : β → m γ}
```

:::syntax Lean.Parser.Term.doSeqItem (title := "Data Dependence in `do`-Notation")
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
{lean}`do let x ← e1; es` is translated to {lean}`e1 >>= fun x => do es`, and fallback clauses are translated to default pattern matches.
{keywordOf Lean.Parser.Term.doLet}`let` may also be used with the standard definition syntax `:=` instead of `←`.
This indicates a pure, rather than monadic, definition:
:::syntax Lean.Parser.Term.doSeqItem (title := "Local Definitions in `do`-Notation")
```grammar
let $v := $e:term
```
:::
{lean}`do let x := e; es` is translated to {lean}`let x := e; do es`.

:::table (header := true)
*
  * {keywordOf Lean.Parser.Term.do}`do` Item
  * Desugaring
*
  * ```leanTerm
    do
    let x ← e1
    es
    ```
  * ```leanTerm
    e1 >>= fun x =>
      do es
    ```
*
  * ```leanTerm
    do
    let some x ← e1?
      | fallback
    es
    ```
  * ```leanTerm
    e1? >>= fun
      | some x => do
        es
      | _ => fallback
    ```
*
  * ```leanTerm
    do
    let x := e
    es
    ```
  * ```leanTerm
    let x := e
    do es
    ```
:::

```lean (show := false) (keep := false)
-- Test desugarings
def ex1a := do
    let x ← e1
    es
def ex1b :=
    e1 >>= fun x =>
      do es
example : @ex1a = @ex1b := by rfl


def ex2a :=
    do
    let some x ← e1?
      | fallback
    es

def ex2b :=
    e1? >>= fun
      | some x => do
        es
      | _ => fallback
example : @ex2a = @ex2b := by rfl

def ex3a :=
    do
    let x := e
    es
def ex3b :=
    let x := e
    do es
example : @ex3a = @ex3b := by rfl
```
Within a {keywordOf Lean.Parser.Term.do}`do` block, `←` may be used as a prefix operator.
The expression to which it is applied is replaced with a fresh variable, which is bound using {name}`bind` just before the current step.
This allows monadic effects to be used in positions that otherwise might expect a pure value, while still maintaining the distinction between _describing_ an effectful computation and actually _executing_ its effects.
Multiple occurrences of `←` are processed from left to right, inside to outside.

::::figure "Example Nested Action Desugarings"
:::table (header := true)
*
  * Example {keywordOf Lean.Parser.Term.do}`do` Item
  * Desugaring
*
  * ```leanTerm
    do
    f (← e1) (← e2)
    es
    ```
  * ```leanTerm
    do
    let x ← e1
    let y ← e2
    f x y
    es
    ```
*
  * ```leanTerm
    do
    let x := g (← h (← e1))
    es
    ```
  * ```leanTerm
    do
    let y ← e1
    let z ← h y
    let x := g z
    es
    ```
:::
::::

```lean (show := false) (keep := false)
-- Test desugarings
def ex1a := do
  f (← e1) (← e2)
  es
def ex1b := do
  let x ← e1
  let y ← e2
  f x y
  es
example : @ex1a = @ex1b := by rfl
def ex2a := do
  let x := g (← h (← e1))
  es
def ex2b := do
  let y ← e1
  let z ← h y
  let x := g z
  es
example : @ex2a = @ex2b := by rfl
```

In addition to convenient support for sequential computations with data dependencies, {keywordOf Lean.Parser.Term.do}`do`-notation also supports the local addition of a variety of effects, including early return, local mutable state, and loops with early termination.
These effects are implemented via transformations of the entire {keywordOf Lean.Parser.Term.do}`do` block in a manner akin to {tech}[monad transformers], rather than via a local desugaring.

## Early Return

Early return terminates a computation immediately with a given value.
The value is returned from the closest containing {keywordOf Lean.Parser.Term.do}`do` block; however, this may not be the closest `do` keyword.
The rules for determining the extent of a {keywordOf Lean.Parser.Term.do}`do` block are described {ref "closest-do-block"}[in their own section].

:::syntax Lean.Parser.Term.doSeqItem (title := "Early Return")
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
:::syntax Lean.Parser.Term.doSeqItem (title := "Local Mutability")
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
%%%
tag := "do-control-structures"
%%%

There are {keywordOf Lean.Parser.Term.do}`do` items that correspond to most of Lean's term-level control structures.
When they occur as a step in a {keywordOf Lean.Parser.Term.do}`do` block, they are interpreted as {keywordOf Lean.Parser.Term.do}`do` items rather than terms.
Each branch of the control structures is a sequence of {keywordOf Lean.Parser.Term.do}`do` items, rather than a term, and some of them are more syntactically flexible than their corresponding terms.

:::syntax Lean.Parser.Term.doSeqItem (title := "Conditionals")
In a {keywordOf Lean.Parser.Term.do}`do` block, {keywordOf Lean.Parser.Term.doIf}`if` statements may omit their {keywordOf Lean.Parser.Term.doIf}`else` branch.
Omitting an {keywordOf Lean.Parser.Term.doIf}`else` branch is equivalent to using {name}`pure`{lean}` ()` as the contents of the branch.
```grammar
if $[$h :]? $e then
  $e*
$[else
  $_*]?
```
:::

Syntactically, the {keywordOf Lean.Parser.Term.doIf}`then` branch cannot be omitted.
For these cases, {keywordOf Lean.Parser.Term.doUnless}`unless` only executes its body when the condition is false.
The {keywordOf Lean.Parser.Term.do}`do` in {keywordOf Lean.Parser.Term.doUnless}`unless` is part of its syntax and does not induce a nested {keywordOf Lean.Parser.Term.do}`do` block.
:::syntax Lean.Parser.Term.doSeqItem (title := "Reverse Conditionals")
```grammar
unless $e do
  $e*
```
:::


When {keywordOf Lean.Parser.Term.doMatch}`match` is used in a {keywordOf Lean.Parser.Term.do}`do` block, each branch is considered to be part of the same block.
Otherwise, it is equivalent to the {keywordOf Lean.Parser.Term.match}`match` term.
:::syntax Lean.Parser.Term.doSeqItem (title := "Pattern Matching")
```grammar
match $[$[$h :]? $e],* with
  $[| $t,* => $e*]*
```
:::


## Iteration
%%%
tag := "monad-iteration-syntax"
%%%

Within a {keywordOf Lean.Parser.Term.do}`do` block, {keywordOf Lean.Parser.Term.doFor}`for`​`…`​{keywordOf Lean.Parser.Term.doFor}`in` loops allow iteration over a data structure.
The body of the loop is part of the containing {keywordOf Lean.Parser.Term.do}`do` block, so local effects such as early return and mutable variables may be used.

:::syntax Lean.Parser.Term.doSeqItem (title := "Iteration over Collections")
```grammar
for $[$[$h :]? $x in $y],* do
  $e*
```
:::

A {keywordOf Lean.Parser.Term.doFor}`for`​`…`​{keywordOf Lean.Parser.Term.doFor}`in` loop requires at least one clause that specifies the iteration to be performed, which consists of an optional membership proof name followed by a colon (`:`), a pattern to bind, the keyword {keywordOf Lean.Parser.Term.doFor}`in`, and a collection term.
The pattern, which may just be an {tech}[identifier], must match any element of the collection; patterns in this position cannot be used as implicit filters.
Further clauses may be provided by separating them with commas.
Each collection is iterated over at the same time, and iteration stops when any of the collections runs out of elements.

:::example "Iteration Over Multiple Collections"
When iterating over multiple collections, iteration stops when any of the collections runs out of elements.
```lean (name := earlyStop)
#eval Id.run do
  let mut v := #[]
  for x in [0:43], y in ['a', 'b'] do
    v := v.push (x, y)
  return v
```
```leanOutput earlyStop
#[(0, 'a'), (1, 'b')]
```
:::

::::keepEnv
:::example "Iteration over Array Indices with {keywordOf Lean.Parser.Term.doFor}`for`"

When iterating over the valid indices for an array with {keywordOf Lean.Parser.Term.doFor}`for`, naming the membership proof allows the tactic that searches for proofs that array indices are in bounds to succeed.
```lean (keep := false)
def satisfyingIndices (p : α → Prop) [DecidablePred p] (xs : Array α) : Array Nat := Id.run do
  let mut out := #[]
  for h : i in [0:xs.size] do
    if p xs[i] then out := out.push i
  return out
```

Omitting the hypothesis name causes the array lookup to fail, because no proof is available in the context that the iteration variable is within the specified range.

```lean (keep := false) (show := false)
-- test it
/--
error: failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
m : Type → Type
inst✝¹ : Monad m
α β γ : Type
e1✝ : m Unit
e : β
es : m α
e1 : m β
e1? : m (Option β)
fallback : m α
e2 : m γ
f : β → γ → m Unit
g : γ → α
h : β → m γ
p : α → Prop
inst✝ : DecidablePred p
xs : Array α
out✝ : Array Nat := #[]
i : Nat
r✝ : Array Nat
out : Array Nat := r✝
⊢ i < xs.size
-/
#check_msgs in
def satisfyingIndices (p : α → Prop) [DecidablePred p] (xs : Array α) : Array Nat := Id.run do
  let mut out := #[]
  for i in [0:xs.size] do
    if p xs[i] then out := out.push i
  return out
```
:::
::::

:::::keepEnv
::::leanSection

Iteration with `for`-loops is translated into uses of `ForIn.forIn`, which is an analogue of `ForM.forM` with added support for local mutations and early termination.
{name}`ForIn.forIn` receives an initial value for the local mutable state and a monadic action as parameters, along with the collection being iterated over.
The monadic action passed to {name}`ForIn.forIn` takes a current state as a parameter and, after carrying out actions in the monad {lean}`m`, returns either {name}`ForInStep.yield` to indicate that iteration should continue with an updated set of local mutable values, or {name}`ForInStep.done` to indicate that {keywordOf Lean.Parser.Term.doBreak}`break` or {keywordOf Lean.Parser.Term.doReturn}`return` was executed.
When iteration is complete, {name}`ForIn.forIn` returns the final values of the local mutable values.

The specific desugaring of a loop depends on how state and early termination are used in its body.
Here are some examples:
```lean (show := false)
axiom «<B>» : Type u
axiom «<b>» : β
variable [Monad m] (xs : Coll) [ForIn m Coll α] [instMem : Membership α Coll] [ForIn' m Coll α instMem]
variable (f : α → β → m β) (f' : (x : α) → x ∈ xs → β → m β)

macro "…" : term => `((«<b>» : β))
```

:::table (header := true)
*
  * {keywordOf Lean.Parser.Term.do}`do` Item
  * Desugaring
*
  * ```leanTerm (type := "m α")
    do
    let mut b := …
    for x in xs do
      b ← f x b
    es
    ```
  * ```leanTerm (type := "m α")
    do
    let b := …
    let b ← ForIn.forIn xs b fun x b => do
      let b ← f x b
      return ForInStep.yield b
    es
    ```
*
  * ```leanTerm (type := "m α")
    do
    let mut b := …
    for x in xs do
      b ← f x b
      break
    es
    ```
  * ```leanTerm (type := "m α")
    do
    let b := …
    let b ← ForIn.forIn xs b fun x b => do
      let b ← f x b
      return ForInStep.done b
    es
    ```
*
  * ```leanTerm (type := "m α")
    do
    let mut b := …
    for h : x in xs do
      b ← f' x h b
    es
    ```
  * ```leanTerm (type := "m α")
    do
    let b := …
    let b ← ForIn'.forIn' xs b fun x h b => do
      let b ← f' x h b
      return ForInStep.yield b
    es
    ```
*
  * ```leanTerm (type := "m α")
    do
    let mut b := …
    for h : x in xs do
      b ← f' x h b
      break
    es
    ```
  * ```leanTerm (type := "m α")
    do
    let b := …
    let b ← ForIn'.forIn' xs b fun x h b => do
      let b ← f' x h b
      return ForInStep.done b
    es
    ```
:::
::::
:::::


The body of a {keywordOf Lean.doElemWhile_Do_}`while` loop is repeated while the condition remains true.
It is possible to write infinite loops using them in functions that are not marked {keywordOf Lean.Parser.Command.declaration}`partial`.
This is because the {keywordOf Lean.Parser.Command.declaration}`partial` modifier only applies to non-termination or infinite regress induced by the function being defined, and not by those that it calls.
The translation of {keywordOf Lean.doElemWhile_Do_}`while` loops relies on a separate helper.

:::syntax Lean.Parser.Term.doSeqItem (title := "Conditional Loops")
```grammar
while $e do
  $e*
```
```grammar
while $h : $e do
  $e*
```
:::

The body of a {keywordOf Lean.doElemRepeat__Until_}`repeat`-{keywordOf Lean.doElemRepeat__Until_}`until` loop is always executed at least once.
After each iteration, the condition is checked, and the loop is repeated when the condition is *false*.
When the condition becomes true, iteration stops.

:::syntax Lean.Parser.Term.doSeqItem (title := "Post-Tested Loops")
```grammar
repeat
  $e*
until $_
```
:::


The body of a {keywordOf Lean.doElemRepeat_}`repeat` loop is repeated until a {keywordOf Lean.Parser.Term.doBreak}`break` statement is executed.
Just like {keywordOf Lean.doElemWhile_Do_}`while` loops, these loops can be used in functions that are not marked {keywordOf Lean.Parser.Command.declaration}`partial`.

:::syntax Lean.Parser.Term.doSeqItem (title := "Unconditional Loops")
```grammar
repeat
  $e*
```
:::

The {keywordOf Lean.Parser.Term.doContinue}`continue` statement skips the rest of the body of the closest enclosing {keywordOf Lean.doElemRepeat_}`repeat`, {keywordOf Lean.doElemWhile_Do_}`while`, or {keywordOf Lean.Parser.Term.doFor}`for` loop, moving on to the next iteration.
The {keywordOf Lean.Parser.Term.doBreak}`break` statement terminates the closest enclosing {keywordOf Lean.doElemRepeat_}`repeat`, {keywordOf Lean.doElemWhile_Do_}`while`, or {keywordOf Lean.Parser.Term.doFor}`for` loop, stopping iteration.

:::syntax Lean.Parser.Term.doSeqItem (title := "Loop Control Statements")
```grammar
continue
```
```grammar
break
```
:::

In addition to {keywordOf Lean.Parser.Term.doBreak}`break`, loops can always be terminated by effects in the current monad.
Throwing an exception from a loop terminates the loop.

:::example "Terminating Loops in the {lean}`Option` Monad"
The {name}`failure` method from the {name}`Alternative` class can be used to terminate an otherwise-infinite loop in the {name}`Option` monad.

```lean (name := natBreak)
#eval show Option Nat from do
  let mut i := 0
  repeat
    if i > 1000 then failure
    else i := 2 * (i + 1)
  return i
```
```leanOutput natBreak
none
```
:::

## Identifying `do` Blocks
%%%
tag := "closest-do-block"
%%%

Many features of {keywordOf Lean.Parser.Term.do}`do`-notation have an effect on the {deftech}[current {keywordOf Lean.Parser.Term.do}`do` block].
In particular, early return aborts the current block, causing it to evaluate to the returned value, and mutable bindings can only be mutated in the block in which they are defined.
Understanding these features requires a precise definition of what it means to be in the “same” block.

Empirically, this can be checked using the Lean language server.
When the cursor is on a {keywordOf Lean.Parser.Term.doReturn}`return` statement, the corresponding {keywordOf Lean.Parser.Term.do}`do` keyword is highlighted.
Attempting to mutate a mutable binding outside of the same {keywordOf Lean.Parser.Term.do}`do` block results in an error message.

:::figure "Highlighting {keywordOf Lean.Parser.Term.do}`do`"

![Highlighting do from return](/static/screenshots/do-return-hl-1.png)

![Highlighting do from return with errors](/static/screenshots/do-return-hl-2.png)
:::

The rules are as follows:
 * Each item immediately nested under the {keywordOf Lean.Parser.Term.do}`do` keyword that begins a block belongs to that block.
 * Each item immediately nested under the {keywordOf Lean.Parser.Term.do}`do` keyword that is an item in a containing {keywordOf Lean.Parser.Term.do}`do` block belongs to the outer block.
 * Items in the branches of an {keywordOf Lean.Parser.Term.doIf}`if`, {keywordOf Lean.Parser.Term.doMatch}`match`, or {keywordOf Lean.Parser.Term.doUnless}`unless` item belong to the same {keywordOf Lean.Parser.Term.do}`do` block as the control structure that contains them. The {keywordOf Lean.Parser.Term.doUnless}`do` keyword that is part of the syntax of {keywordOf Lean.Parser.Term.doUnless}`unless` does not introduce a new {keywordOf Lean.Parser.Term.do}`do` block.
 * Items in the body of {keywordOf Lean.doElemRepeat_}`repeat`, {keywordOf Lean.doElemWhile_Do_}`while`, and {keywordOf Lean.Parser.Term.doFor}`for` belong to the same {keywordOf Lean.Parser.Term.do}`do` block as the loop  that contains them. The {keywordOf Lean.Parser.Term.doFor}`do` keyword that is part of the syntax of {keywordOf Lean.doElemWhile_Do_}`while` and {keywordOf Lean.Parser.Term.doFor}`for` does not introduce a new {keywordOf Lean.Parser.Term.do}`do` block.

```lean (show := false)
-- Test nested `do` rules

/-- info: ((), 6) -/
#check_msgs in
#eval (·.run 0) <| show StateM Nat Unit from do
  set 5
  do
    set 6
    return

/-- error: must be last element in a `do` sequence -/
#check_msgs in
#eval (·.run 0) <| show StateM Nat Unit from do
  set 5
  do
    set 6
    return
  set 7
  return

/-- info: ((), 6) -/
#check_msgs in
#eval (·.run 0) <| show StateM Nat Unit from do
  set 5
  if true then
    set 6
    do return
  set 7
  return
```

::::keepEnv
:::example "Nested `do` and Branches"
The following example outputs {lean}`6` rather than {lean}`7`:
```lean (name := nestedDo)
def test : StateM Nat Unit := do
  set 5
  if true then
    set 6
    do return
  set 7
  return

#eval test.run 0
```
```leanOutput nestedDo
((), 6)
```

This is because the {keywordOf Lean.Parser.Term.doReturn}`return` statement under the {keywordOf Lean.Parser.Term.doIf}`if` belongs to the same {keywordOf Lean.Parser.Term.do}`do` as its immediate parent, which itself belongs to the same {keywordOf Lean.Parser.Term.do}`do` as the {keywordOf Lean.Parser.Term.doIf}`if`.
If {keywordOf Lean.Parser.Term.do}`do` blocks that occurred as items in other {keywordOf Lean.Parser.Term.do}`do` blocks instead created new blocks, then the example would output {lean}`7`.
:::
::::

```lean (show := false)
end
```

```lean (show := false)
-- tests for this section
set_option pp.all true

/--
info: @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) Unit α e1 fun (x : PUnit.{1}) => es : m α
-/
#check_msgs in
#check do e1; es

section
variable {e1 : m β}
/-- info: @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) β α e1 fun (x : β) => es : m α -/
#check_msgs in
#check do let x ← e1; es
end

/--
info: let x : β := e;
es : m α
-/
#check_msgs in
#check do let x := e; es

variable {e1 : m β} {e2 : m γ} {f : β → γ → m Unit} {g : γ → α} {h : β → m γ}

/--
info: @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) β α e1 fun (__do_lift : β) =>
  @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) γ α e2 fun (__do_lift_1 : γ) =>
    @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) Unit α (f __do_lift __do_lift_1) fun (x : PUnit.{1}) => es : m α
-/
#check_msgs in
#check do f (← e1) (← e2); es

/--
info: @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) β α e1 fun (__do_lift : β) =>
  @Bind.bind.{0, 0} m (@Monad.toBind.{0, 0} m inst✝) γ α (h __do_lift) fun (__do_lift : γ) =>
    let x : α := g __do_lift;
    es : m α
-/
#check_msgs in
#check do let x := g (← h (← e1)); es

end


```

## Type Classes for Iteration

To be used with {keywordOf Lean.Parser.Term.doFor}`for` loops without membership proofs, collections must implement the {name}`ForIn` type class.
Implementing {lean}`ForIn'` additionally allows the use of {keywordOf Lean.Parser.Term.doFor}`for` loops with membership proofs.

{docstring ForIn}

{docstring ForIn'}

{docstring ForInStep}

{docstring ForInStep.value}

{docstring ForM}

{docstring ForM.forIn}
