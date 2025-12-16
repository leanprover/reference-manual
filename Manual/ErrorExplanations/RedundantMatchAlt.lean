/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella, Rob Simmons
-/
import VersoManual
import Manual.Meta.ErrorExplanation

open Lean
open Verso.Genre Manual InlineLean

#doc (Manual) "About: `redundantMatchAlt`" =>
%%%
shortTitle := "redundantMatchAlt"
%%%

{errorExplanationHeader lean.redundantMatchAlt}

This error occurs when an alternative in a pattern match can never be reached: any values that would
match the provided patterns would also match some preceding alternative. Refer to the
{ref "pattern-matching"}[Pattern Matching] manual section for additional details
about pattern matching.

This error may appear in any pattern matching expression, including
{keywordOf Lean.Parser.Term.match}`match` expressions, equational function definitions, `if let`
bindings, and monadic {keywordOf Lean.Parser.Term.let}`let` bindings with fallback clauses.

In pattern-matches with multiple arms, this error may occur if a less-specific pattern precedes a
more-specific one that it subsumes. Bear in mind that expressions are matched against patterns from
top to bottom, so specific patterns should precede generic ones.

In `if let` bindings and monadic {keywordOf Lean.Parser.Term.let}`let` bindings with fallback
clauses, in which only one pattern is specified, this error indicates that the specified pattern
will always be matched. In this case, the binding in question can be replaced with a standard
pattern-matching {keywordOf Lean.Parser.Term.let}`let`.

One common cause of this error is that a pattern that was intended to match a constructor was
instead interpreted as a variable binding. This occurs, for instance, if a constructor
name (e.g., `cons`) is written without its prefix ({name}`List`) outside of that type's namespace.
The constructor-name-as-variable linter, enabled by default, will display a warning on any variable
patterns that resemble constructor names.

This error nearly always indicates an issue with the code where it appears. If needed, however,
`set_option match.ignoreUnusedAlts true` will disable the check for this error and allow pattern
matches with redundant alternatives to be compiled by discarding the unused arms.

# Examples

:::errorExample "Incorrect Ordering of Pattern Matches"
```broken
def seconds : List (List α) → List α
  | [] => []
  | _ :: xss => seconds xss
  | (_ :: x :: _) :: xss => x :: seconds xss
```
```output
Redundant alternative: Any expression matching
  (head✝ :: x :: tail✝) :: xss
will match one of the preceding alternatives
```
```fixed
def seconds : List (List α) → List α
  | [] => []
  | (_ :: x :: _) :: xss => x :: seconds xss
  | _ :: xss => seconds xss
```

Since any expression matching `(_ :: x :: _) :: xss` will also match `_ :: xss`, the last
alternative in the broken implementation is never reached. We resolve this by moving the more
specific alternative before the more general one.
:::

:::errorExample "Unnecessary Fallback Clause"
```broken
example (p : Nat × Nat) : IO Nat := do
  let (m, n) := p
    | return 0
  return m + n
```
```output
Redundant alternative: Any expression matching
  x✝
will match one of the preceding alternatives
```
```fixed
example (p : Nat × Nat) : IO Nat := do
  let (m, n) := p
  return m + n
```

Here, the fallback clause serves as a catch-all for all values of `p` that do not match `(m, n)`.
However, no such values exist, so the fallback clause is unnecessary and can be removed. A similar
error arises when using `if let pat := e` when `e` will always match `pat`.
:::

:::errorExample "Pattern Treated as Variable, Not Constructor"
```broken
example (xs : List Nat) : Bool :=
  match xs with
  | nil => false
  | _ => true
```
```output
Redundant alternative: Any expression matching
  x✝
will match one of the preceding alternatives
```
```fixed
example (xs : List Nat) : Bool :=
  match xs with
  | .nil => false
  | _ => true
```

In the original example, `nil` is treated as a variable, not as a constructor name, since this
definition is not within the {name}`List` namespace. Thus, all values of `xs` will match the first
pattern, rendering the second unused. Notice that the constructor-name-as-variable linter displays a
warning at `nil`, indicating its similarity to a valid constructor name. Using dot-prefix notation,
as shown in the fixed example, or specifying the full constructor name {name}`List.nil`
achieves the intended behavior.
:::
