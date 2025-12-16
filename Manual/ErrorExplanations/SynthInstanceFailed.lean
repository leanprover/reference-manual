/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rob Simmons
-/
import VersoManual
import Manual.Meta.ErrorExplanation

open Lean
open Verso.Genre Manual InlineLean

#doc (Manual) "About: `synthInstanceFailed`" =>
%%%
shortTitle := "synthInstanceFailed"
%%%

{errorExplanationHeader lean.synthInstanceFailed}

```lean -show
variable {t : Type}
```

{ref "type-classes"}[Type classes] are the mechanism that Lean and many other
programming languages use to handle overloaded operations. The code that handles a particular
overloaded operation is an _instance_ of a typeclass; deciding which instance to use for a given
overloaded operation is called _synthesizing_ an instance.

As an example, when Lean encounters an expression `x + y` where `x` and `y` both have type
{name}`Int`, it is necessary to look up how it should add two integers and also look up what the
resulting type will be. This is described as synthesizing an instance of the type class
{lean}`HAdd Int Int t` for some type `t`.

Many failures to synthesize an instance of a type class are the result of using the wrong binary
operation. Both success and failure are not always straightforward, because some instances are
defined in terms of other instances, and Lean must recursively search to find appropriate instances.
It's possible to {ref "instance-search"}[inspect Lean's instance synthesis], and this
can be helpful for diagnosing tricky failures of type class instance synthesis.

# Examples

:::errorExample "Using the Wrong Binary Operation"

```broken
#eval "A" + "3"
```
```output
failed to synthesize instance of type class
  HAdd String String ?m.4

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
```fixed
#eval "A" ++ "3"
```

The binary operation `+` is associated with the {name}`HAdd` type class, and there's no way to add
two strings. The binary operation `++`, associated with the {name}`HAppend` type class, is the
correct way to append strings.
:::

:::errorExample "Arguments Have the Wrong Type"

```broken
def x : Int := 3
#eval x ++ "meters"
```
```output
failed to synthesize instance of type class
  HAppend Int String ?m.4

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
```
```fixed
def x : Int := 3
#eval ToString.toString x ++ "meters"
```

Lean does not allow integers and strings to be added directly. The function
{name}`ToString.toString` uses type class overloading to convert values to strings; by successfully
searching for an instance of {lean}`ToString Int`, the second example will succeed.
:::

:::errorExample "Missing Type Class Instance"

```broken
inductive MyColor where
  | chartreuse | sienna | thistle

def forceColor (oc : Option MyColor) :=
  oc.get!
```
```output
failed to synthesize instance of type class
  Inhabited MyColor

Hint: Adding the command `deriving instance Inhabited for MyColor` may allow Lean to derive the missing instance.
```
```fixed "derive instance when defining type"
inductive MyColor where
  | chartreuse | sienna | thistle
deriving Inhabited

def forceColor (oc : Option MyColor) :=
  oc.get!
```
```fixed "derive instance separately"
inductive MyColor where
  | chartreuse | sienna | thistle

deriving instance Inhabited for MyColor

def forceColor (oc : Option MyColor) :=
  oc.get!
```
```fixed "define instance"
inductive MyColor where
  | chartreuse | sienna | thistle

instance : Inhabited MyColor where
  default := .sienna

def forceColor (oc : Option MyColor) :=
  oc.get!
```

Type class synthesis can fail because an instance of the type class simply needs to be provided.
This commonly happens for type classes like {name}`Repr`, {name}`BEq`, {name}`ToJson` and
{name}`Inhabited`. Lean can often {ref "deriving-instances"}[automatically generate instances of the
type class with the `deriving` keyword] either when the type is defined or with the stand-alone
{keywordOf Lean.Parser.Command.deriving}`deriving` command.
:::
