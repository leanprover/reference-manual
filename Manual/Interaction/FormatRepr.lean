/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Std.Data.HashSet

import Manual.Meta
import Manual.Papers

open Lean.MessageSeverity

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

set_option verso.code.warnLineLength 72
set_option verso.docstring.allowMissing true

#doc (Manual) "Formatted Output" =>
%%%
tag := "format-repr"
%%%

The {name}`Repr` type class is used to provide a standard representation for data that can be parsed and evaluated to obtain an equivalent value.
This is not a strict correctness criterion: for some types, especially those with embedded propositions, it is impossible to achieve.
However, the output produced by a {name}`Repr` instance should be as close as possible to something that can be parsed and evaluated.

:::paragraph
In addition to being machine-readable, this representation should be convenient for humans to understand—in particular, lines should not be too long, and nested values should be indented.
This is achieved through a two-step process:

 1. The {name}`Repr` instance produces an intermediate document of type {name}`Std.Format`, which compactly represents a _set_ of strings that differ with respect to the placement of newlines and indentation.
 2. A rendering process selects the “best” representative from the set, according to criteria such as a desired maximum line length.

In particular, {name}`Std.Format` can be built compositionally, so {name}`Repr` instances don't need to take the surrounding indentation context into account.
:::


# Format
%%%
tag := "Format"
%%%


::::leanSection
```lean show:=false
open Std (Format)
open Std.Format
variable {str : String} {indent : String} {n : Nat}
```
:::paragraph
A {name}`Format`{margin}[The API described here is an adaptation of Wadler's ({citehere wadler2003}[]) It has been modified to be efficient in a strict language and with support for additional features such as metadata tags.] is a compact representation of a set of strings.
The most important {name Std.Format}`Format` operations are:

: Strings

  A {name}`String` can be made into a {name}`Format` using the {name}`text` constructor.
  This constructor is registered as a {ref "coercions"}[coercion] from {name}`String` to {name}`Format`, so it is often unnecessary to invoke it explicitly.
  {lean}`text str` represents the singleton set that contains only {lean}`str`.
  If the string contains newline characters ({lean}`'\n'`), then they are unconditionally inserted as newlines into the resulting output, regardless of groups.
  They are, however, indented according to the current indentation level.

: Appending

  Two {name}`Format`s can be appended using the `++` operator from the {inst}`Append Format` instance.

: Groups and Newlines

  The constructor {name}`line` represents the set that contains both {lean}`"\n" ++ indent` and {lean}`" "`, where {lean}`indent` is a string with enough spaces to indent the line correctly.
  Imperatively, it can be thought of as a newline that will be “flattened” to a space if there is sufficient room on the current line.
  Newlines occur in _groups_: the nearest enclosing application of the {name}`group` operator determines which group the newline belongs to.
  By default, either all {name}`line`s in a group represent {lean}`"\n"` or all represent {lean}`" "`; groups may also be configured to fill lines, in which case the minimal number of {name}`line`s in the group represent {lean}`"\n"`.
  Uses of {name}`line` that do not belong to a group always represent {lean}`"\n"`.

: Indentation

  When a newline is inserted, the output is also indented.
  {lean}`nest n` increases the indentation of a document by {lean}`n` spaces.
  This is not sufficient to represent all Lean syntax, which sometimes requires that columns align exactly.
  {lean}`align` is a document that ensures that the output string is at the current indentation level, inserting just spaces if possible, or a newline followed by spaces if needed.

: Tagging

  Lean's interactive features require the ability to associate output with the underlying values that they represent.
  This allows Lean development environments to present elaborated terms when hovering over terms proof states or error messages, for example.
  Documents can be _tagged_ with a {name}`Nat` value {lean}`n` using {lean}`tag n`; these {name}`Nat`s should be mapped to the underlying value in a side table.
:::
::::

:::example "Widths and Newlines"
```lean
open Std Format
```

The helper {name}`parenSeq` creates a parenthesized sequence, with grouping and indentation to make it responsive to different output widths.
```lean
def parenSeq (xs : List Format) : Format :=
  group <|
    nest 2 (text "(" ++ line ++ joinSep xs line) ++
    line ++
    ")"
```

This document represents a parenthesized sequence of numbers:
```lean
def lst : Format := parenSeq nums
where nums := [1, 2, 3, 4, 5].map (text s!"{·}")
```

```lean show := false
-- check statement in next paragraph
/-- info: 120 -/
#check_msgs in
#eval defWidth
```

Rendering it with the default line width of 120 characters places the entire sequence on one line:
```lean (name := lstp)
#eval IO.println lst.pretty
```
```leanOutput lstp
( 1 2 3 4 5 )
```

Because all the {name}`line`s belong to the same {name}`group`, they will either all be rendered as spaces or all be rendered as newlines.
If only 9 characters are available, all of the {name}`line`s in {name}`lst` become newlines:
```lean (name := lstp9)
#eval IO.println (lst.pretty (width := 9))
```
```leanOutput lstp9
(
  1
  2
  3
  4
  5
)
```


This document contains three copies of {name}`lst` in a further parenthesized sequence:
```lean
def lsts := parenSeq [lst, lst, lst]
```

At the default width, it remains on one line:
```lean (name := lstsp)
#eval IO.println lsts.pretty
```
```leanOutput lstsp
( ( 1 2 3 4 5 ) ( 1 2 3 4 5 ) ( 1 2 3 4 5 ) )
```

If only 20 characters are available, each occurrence of {name}`lst` ends up on its own line.
This is because converting the outer {name}`group` to newlines is sufficient to keep the string within 20 columns:
```lean (name := lstsp20)
#eval IO.println (lsts.pretty (width := 20))
```
```leanOutput lstsp20
(
  ( 1 2 3 4 5 )
  ( 1 2 3 4 5 )
  ( 1 2 3 4 5 )
)
```

If only 10 characters are available, each number must be on its own line:
```lean (name := lstsp10)
#eval IO.println (lsts.pretty (width := 10))
```
```leanOutput lstsp10
(
  (
    1
    2
    3
    4
    5
  )
  (
    1
    2
    3
    4
    5
  )
  (
    1
    2
    3
    4
    5
  )
)
```
:::


:::example "Grouping and Filling"
```lean
open Std Format
```

The helper {name}`parenSeq` creates a parenthesized sequence, with each element placed on a new line and indented:
```lean
def parenSeq (xs : List Format) : Format :=
  nest 2 (text "(" ++ line ++ joinSep xs line) ++
  line ++
  ")"
```

{name}`nums` contains the numbers one through twenty, as a list of formats:
```lean
def nums : List Format := Nat.fold 20 (init := []) fun i _ ys => text s!"{20 - i}" :: ys
```

```lean (name := nums)
#eval nums
```

Because {name}`parenSeq` does not introduce any groups, the resulting document is rendered on a single line:
```lean
#eval IO.println (pretty (parenSeq nums))
```

This can be fixed by grouping them.
{name}`grouped` does so with {name}`group`, while {name}`filled` does so with {name}`fill`.
```lean
def grouped := group (parenSeq nums)
def filled := fill (parenSeq nums)
```

Both grouping operators cause uses of {name}`line` to render as spaces.
Given sufficient space, both render on a single line:
```lean (name := groupedp)
#eval IO.println (pretty grouped)
```
```leanOutput groupedp
( 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 )
```

```lean (name := filledp)
#eval IO.println (pretty filled)
```
```leanOutput filledp
( 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 )
```

However, difference become apparent when there is not sufficient space on a single line.
Unless _all_ newlines in a {name}`group` can be spaces, none can:
```lean (name := groupedp30)
#eval IO.println (pretty (width := 30) grouped)
```
```leanOutput groupedp30
(
  1
  2
  3
  4
  5
  6
  7
  8
  9
  10
  11
  12
  13
  14
  15
  16
  17
  18
  19
  20
)
```

Using {name}`fill`, on the other hand, only inserts newlines as required to avoid being two wide:
```lean (name := filledp30)
#eval IO.println (pretty (width := 30) filled)
```
```leanOutput filledp30
( 1 2 3 4 5 6 7 8 9 10 11 12
  13 14 15 16 17 18 19 20 )
```

The behavior of {name}`fill` can be seen clearly with longer sequences:
```lean (name := filledbigp30)
#eval IO.println (pretty (width := 30) (fill (parenSeq (nums ++ nums ++ nums ++ nums))))
```
```leanOutput filledbigp30
( 1 2 3 4 5 6 7 8 9 10 11 12
  13 14 15 16 17 18 19 20 1 2
  3 4 5 6 7 8 9 10 11 12 13 14
  15 16 17 18 19 20 1 2 3 4 5
  6 7 8 9 10 11 12 13 14 15 16
  17 18 19 20 1 2 3 4 5 6 7 8
  9 10 11 12 13 14 15 16 17 18
  19 20 )
```
:::

::::example "Newline Characters in Strings"
Including a newline character in a string causes the rendering process to unconditionally insert a newline.
These newlines do, however, respect the current indentation level.

The document {name}`str` consists of an embedded string with two newlines:
```lean
open Std Format

def str : Format := text "abc\nxyz\n123"
```

:::paragraph
Printing the string both with and without grouping results in the newlines being used:
```lean (name := str1)
#eval IO.println str.pretty
```
```leanOutput str1
abc
xyz
123
```
```lean (name := str2)
#eval IO.println (group str).pretty
```
```leanOutput str2
abc
xyz
123
```
:::

:::paragraph
Because the string does not terminate with a newline, the last line of the first string is on the same line as the first line of the second string:
```lean (name := str3)
#eval IO.println (str ++ str).pretty
```
```leanOutput str3
abc
xyz
123abc
xyz
123
```
:::

:::paragraph
Increasing the indentation level, however, causes all three lines of the string to begin at the same column:
```lean (name := str4)
#eval IO.println (text "It is:" ++ indentD str).pretty
```
```leanOutput str4
It is:
  abc
  xyz
  123
```

```lean (name := str5)
#eval IO.println (nest 8 <| text "It is:" ++ align true ++ str).pretty
```
```leanOutput str5
It is:  abc
        xyz
        123
```
:::

::::

## Documents
%%%
tag := "format-api"
%%%

{docstring Std.Format}

{docstring Std.Format.FlattenBehavior}

{docstring Std.Format.fill}

## Empty Documents
%%%
tag := "format-empty"
%%%


:::paragraph
The empty string does not have a single unique representative in {name}`Std.Format`.
All of the following represent the empty string:

* {lean type:="Std.Format"}`.nil`
* {lean type:="Std.Format"}`.text ""`
* {lean type:="Std.Format"}`.text "" ++ .nil`
* {lean type:="Std.Format"}`.nil ++ .text ""`

Use {name}`Std.Format.isEmpty` to check whether a document contains zero characters, and {name}`Std.Format.isNil` to specifically check whether it is the constructor {lean}`Std.Format.nil`.
:::

{docstring Std.Format.isEmpty}

{docstring Std.Format.isNil}



## Sequences
%%%
tag := "format-join"
%%%

The operators in this section are useful when there is some kind of repeated content, such as the elements of a list.
This is typically done by including {name Std.Format.line}`line` in their separator parameters, using a {ref "format-brackets"}[bracketing operator]

{docstring Std.Format.join}

{docstring Std.Format.joinSep}

{docstring Std.Format.prefixJoin}

{docstring Std.Format.joinSuffix}

## Indentation
%%%
tag := "format-indent"
%%%

These operators make it easier to achieve a consistent indentation style on top of {name}`Std.Format.nest`.

{docstring Std.Format.nestD}

{docstring Std.Format.defIndent}

{docstring Std.Format.indentD}

## Brackets and Parentheses
%%%
tag := "format-brackets"
%%%

These operators make it easier to achieve a consistent parenthesization style.

{docstring Std.Format.bracket}

{docstring Std.Format.sbracket}

{docstring Std.Format.paren}

{docstring Std.Format.bracketFill}

## Rendering
%%%
tag := "format-render"
%%%

The {inst}`ToString Std.Format` instance invokes {name}`Std.Format.pretty` with its default arguments.

There are two ways to render a document:
* Use {name Std.Format.pretty}`pretty` to construct a {name}`String`.
  The entire string must be constructed up front before any can be sent to a user.
* Use {name Std.Format.prettyM}`prettyM` to incrementally emit the {name}`String`, using effects in some {name}`Monad`.
  As soon as each line is rendered, it is emitted.
  This is suitable for streaming output.

{docstring Std.Format.pretty}

{docstring Std.Format.defWidth}

{docstring Std.Format.prettyM}

{docstring Std.Format.MonadPrettyFormat}

## The `ToFormat` Class

The {name}`Std.ToFormat` class is used to provide a standard means to format a value, with no expectation that this formatting be valid Lean syntax.
These instances are used in error messages and by some of the {ref "format-join"}[sequence concatenation operators].

{docstring Std.ToFormat}

# `Repr`
%%%
tag := "repr"
%%%

A {name}`Repr` instance describes how to represent a value as a {name}`Std.Format`.
Because they should emit valid Lean syntax, these instances need to take {tech}[precedence] into account.
Inserting the maximal number of parentheses would work, but it makes it more difficult for humans to read the resulting output.

{docstring Repr}

{docstring repr}

{docstring reprStr}

:::example "Maximal Parentheses"
The type {name}`NatOrInt` can contain a {name}`Nat` or an {name}`Int`:
```lean
inductive NatOrInt where
  | nat : Nat → NatOrInt
  | int : Int → NatOrInt
```
This {inst}`Repr NatOrInt` instance ensures that the output is valid Lean syntax by inserting many parentheses:
```lean
instance : Repr NatOrInt where
  reprPrec x _ :=
    .nestD <| .group <|
      match x with
      | .nat n =>
          .text "(" ++ "NatOrInt.nat" ++ .line ++ "(" ++ repr n ++ "))"
      | .int i =>
          .text "(" ++ "NatOrInt.int" ++ .line ++ "(" ++ repr i ++ "))"
```
Whether it contains a {name}`Nat`, a non-negative {name}`Int`, or a negative {name}`Int`, the result can be parsed:
```lean (name := parens)
open NatOrInt in
#eval do
  IO.println <| repr <| nat 3
  IO.println <| repr <| int 5
  IO.println <| repr <| int (-5)
```
```leanOutput parens
(NatOrInt.nat (3))
(NatOrInt.int (5))
(NatOrInt.int (-5))
```
However, {lean}`(NatOrInt.nat (3))` is not particularly idiomatic Lean, and redundant parentheses can make it difficult to read large expressions.
:::


The method {name}`Repr.reprPrec` has the following signature:
```signature
Repr.reprPrec.{u} {α : Type u} [Repr α] : α → Nat → Std.Format
```
The first explicit parameter is the value to be represented, while the second is the {tech}[precedence] of the context in which it occurs.
This precedence can be used to decide whether to insert parentheses: if the precedence of the syntax being produced by the instance is greater than that of its context, parentheses are necessary.

## How To Write a `Repr` Instance
%%%
tag := "repr-instance-howto"
%%%

Lean can produce an appropriate {name}`Repr` instance for most types automatically using {ref "deriving-instances"}[instance deriving].
In some cases, however, it's necessary to write an instance by hand:

* Some libraries provide functions as the primary instance to a type, rather than its constructors; in these cases, the {name}`Repr` instance should represent a call to these functions.
  For example, {name}`Std.HashSet.ofList` is used in the {inst}`Repr (HashSet α)` instance.

* Some inductive types include well-formedness proofs.
  Because programs can't inspect proofs, they cannot be rendered directly.
  This is a common reason why a type would have an interface other than its constructors.

* Types with special syntax, such as {name}`List`, should use this syntax in their {name}`Repr` isntances.

* The derived {name}`Repr` instance for structures uses {tech}[structure instance] notation.
  A hand-written instance can use the constructor's name explicitly or use {tech}[anonymous constructor syntax].

```lean (show := false)
/-- info: Std.HashSet.ofList [0, 3, 5] -/
#check_msgs in
#eval IO.println <| repr (({} : Std.HashSet Nat).insert 3 |>.insert 5 |>.insert 0)
```
```lean (show := false) (keep := false)
structure S where
  x : Nat
  y : Nat
deriving Repr
/-- info: { x := 2, y := 3 } -/
#check_msgs in
#eval IO.println <| repr <| S.mk 2 3
```

When writing a custom {name}`Repr` instance, please follow these conventions:

: Precedence

  Check precedence, adding parentheses as needed, and pass the correct precedence to the {name}`reprPrec` instances of embedded data.
  Each instance is responsible for surrounding itself in parentheses if needed; instances should generally not parenthesize recursive calls to {name}`reprPrec`.

  Function application has the maximum precedence, {lean}`max_prec`.
  The helpers {name}`Repr.addAppParen` and {name}`reprArg` respectively insert parentheses around applications when needed and pass the appropriate precedence to function arguments.

: Fully-Qualified Names

  A {name}`Repr` instance does have access to the set of open namespaces in a given position.
  All names of constants in the environment should be fully qualified to remove ambiguity.

: Default Nesting

  Nested data should be indented using {name Std.Format.nestD}`nestD` to ensure consistent indentation across instances.

: Grouping and Line Breaks

  The output of every {name}`Repr` instance that includes line breaks should be surrounded in a {name Std.Format.group}`group`.
  Furthermore, if the resulting code contains notional expressions that are nested, a {name Std.Format.group}`group` should be inserted around each nested level.
  Line breaks should usually be inserted in the following positions:
    * Between a constructor and each of its arguments
    * After `:=`
    * After `,`
    * Between the opening and closing braces of {tech}[structure instance] notation and its contents
    * After, but not before, an infix operator

: Parentheses and Brackets

  Parentheses and brackets should be inserted using {name}`Std.Format.bracket` or its specializations {name}`Std.Format.paren` for parentheses and {name}`Std.Format.sbracket` for square brackets.
  These operators align the contents of the parenthesized or bracketed expression in the same way that Lean's do.
  Trailing parentheses and brackets should not be placed on their own line, but rather stay with their contents.

{docstring Repr.addAppParen}

{docstring reprArg}


:::example "Inductive Types with Constructors"
The inductive type {name}`N.NatOrInt` can contain a {name}`Nat` or an {name}`Int`:
```lean
namespace N

inductive NatOrInt where
  | nat : Nat → NatOrInt
  | int : Int → NatOrInt

```
The {inst}`Repr NatOrInt` instance adheres to the conventions:
 * The right-hand side is a function application, so it uses {name}`Repr.addAppParen` to add parentheses if necessary.
 * Parentheses are wrapped around the entire body with no additional {name Std.Format.line}`line`s.
 * The entire function application is grouped, and it is nested the default amount.
 * The function is separated from its parameters by a use of {name Std.Format.line}`line`; this newline will usually be a space because the {inst}`Repr Nat` and {inst}`Repr Int` instances are unlikely to produce long output.
 * Recursive calls to {name}`reprPrec` pass {lean}`max_prec` because they are in function parameter positions, and function application has the highest precedence.

```lean
instance : Repr NatOrInt where
  reprPrec
    | .nat n =>
      Repr.addAppParen <|
        .group <| .nestD <|
          "N.NatOrInt.nat" ++ .line ++ reprPrec n max_prec
    | .int i =>
      Repr.addAppParen <|
        .group <| .nestD <|
          "N.NatOrInt.int" ++ .line ++ reprPrec i max_prec
```
```lean (name := nat5)
#eval IO.println (repr (NatOrInt.nat 5))
```
```leanOutput nat5
N.NatOrInt.nat 5
```
```lean (name := int5)
#eval IO.println (repr (NatOrInt.int 5))
```
```leanOutput int5
N.NatOrInt.int 5
```
```lean (name := intm5)
#eval IO.println (repr (NatOrInt.int (-5)))
```
```leanOutput intm5
N.NatOrInt.int (-5)
```
```lean (name := someintm5)
#eval IO.println (repr (some (NatOrInt.int (-5))))
```
```leanOutput someintm5
some (N.NatOrInt.int (-5))
```


```lean (name := lstnat)
#eval IO.println (repr <| (List.range 10).map (NatOrInt.nat))
```
```leanOutput lstnat
[N.NatOrInt.nat 0,
 N.NatOrInt.nat 1,
 N.NatOrInt.nat 2,
 N.NatOrInt.nat 3,
 N.NatOrInt.nat 4,
 N.NatOrInt.nat 5,
 N.NatOrInt.nat 6,
 N.NatOrInt.nat 7,
 N.NatOrInt.nat 8,
 N.NatOrInt.nat 9]
```

```lean (name := lstnat3)
#eval IO.println (Std.Format.pretty (width := 3) (repr <| (List.range 10).map (NatOrInt.nat)))
```
```leanOutput lstnat3
[N.NatOrInt.nat
   0,
 N.NatOrInt.nat
   1,
 N.NatOrInt.nat
   2,
 N.NatOrInt.nat
   3,
 N.NatOrInt.nat
   4,
 N.NatOrInt.nat
   5,
 N.NatOrInt.nat
   6,
 N.NatOrInt.nat
   7,
 N.NatOrInt.nat
   8,
 N.NatOrInt.nat
   9]
```

:::

:::example "Infix Syntax"
```lean
inductive AddExpr where
  | nat : Nat → AddExpr
  | add : AddExpr → AddExpr → AddExpr

instance : OfNat AddExpr n where
  ofNat := .nat n

instance : Add AddExpr where
  add := .add

protected def AddExpr.reprPrec : AddExpr → Nat → Std.Format
  | .nat n, p  =>
    Repr.reprPrec n p
  | .add e1 e2, p =>
    let out : Std.Format :=
      .nestD <| .group <|
        AddExpr.reprPrec e1 64 ++ " " ++ "+" ++ .line ++
        AddExpr.reprPrec e2 65
    if p ≥ 65 then out.paren else out

instance : Repr AddExpr := ⟨AddExpr.reprPrec⟩
```

```lean (show := false)
-- Test that the guidelines provided for infix operators match Lean's own pretty printer
/--
info: 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 1 + 2 + 3 + 4 + 5 + 6 + 7 +
        8 +
      9 +
    10 +
  11 : Nat
-/
#check_msgs in
#check 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11

/--
info: 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 1 + 2 + 3 + 4 + 5 + 6 + 7 +
        8 +
      9 +
    10 +
  11
-/
#check_msgs in
#eval (1 : AddExpr) + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11

```

```lean
#eval IO.println (repr (((2 + 3) + 4) : AddExpr))
#eval IO.println (repr ((2 + 3 + 4) : AddExpr))
#eval IO.println (repr ((2 + (3 + 4)) : AddExpr))
#eval IO.println (repr ([2 + (3 + 4), (2 + 3) + 4] : List AddExpr))
#eval IO.println <| (repr ([2 + (3 + 4), (2 + 3) + 4] : List AddExpr)).pretty (width := 0)
```
:::

## Atomic Types
%%%
tag := "ReprAtom"
%%%

When the elements of a list are sufficiently small, it can be both difficult to read and wasteful of space to render the list with one element per line.
To improve readability, {name}`List` has two {name}`Repr` instances: one that uses {name}`Std.Format.bracket` for its contents, and one that uses {name}`Std.Format.bracketFill`.
The latter is defined after the former and is thus selected when possible; however, it requires an instance of the empty type class {name}`ReprAtom`.

If the {name}`Repr` instance for a type never generates spaces or newlines, then it should have a {name}`ReprAtom` instance.
Lean has {name}`ReprAtom` instances for types such as {name}`String`, {name}`UInt8`, {name}`Nat`, {name}`Char`, and {name}`Bool`.

```lean (show := false)
open Lean Elab Command in
#eval show CommandElabM Unit from
  for x in [``String, ``UInt8, ``Nat, ``Char, ``Bool] do
    runTermElabM fun _ => do
      discard <| Meta.synthInstance (.app (.const ``ReprAtom [0]) (.const x []))
      Term.synthesizeSyntheticMVarsNoPostponing
```

{docstring ReprAtom}

::::example "Atomic Types and `Repr`"

All constructors of the inductive type {name}`ABC` are without parameters:

```lean
inductive ABC where
  | a
  | b
  | c
deriving Repr
```

The derived {inst}`Repr ABC` instance is used to display lists:
```lean (name := abc1)
def abc : List ABC := [.a, .b, .c]

def abcs : List ABC := abc ++ abc ++ abc

#eval IO.println ((repr abcs).pretty (width := 14))
```

Because of the narrow width, line breaks are inserted:
```leanOutput abc1
[ABC.a,
 ABC.b,
 ABC.c,
 ABC.a,
 ABC.b,
 ABC.c,
 ABC.a,
 ABC.b,
 ABC.c]
```

:::paragraph
However, converting the list to a {lean}`List Nat` leads to a differently-formatted result.
```lean (name := abc2)
def ABC.toNat : ABC → Nat
  | .a => 0
  | .b => 1
  | .c => 2

#eval IO.print ((repr (abcs.map ABC.toNat)).pretty (width := 14))
```
There are far fewer line breaks:
```leanOutput abc2
[0, 1, 2, 0,
 1, 2, 0, 1,
 2]
```
:::

This is because of the existence of a {inst}`ReprAtom Nat` instance.
Adding one for {name}`ABC` leads to similar behavior:
```lean (name := abc3)
instance : ReprAtom ABC := ⟨⟩

#eval IO.println ((repr abcs).pretty (width := 14))
```
```leanOutput abc3
[ABC.a, ABC.b,
 ABC.c, ABC.a,
 ABC.b, ABC.c,
 ABC.a, ABC.b,
 ABC.c]
```
::::
