/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Lean.MessageSeverity

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Introduction" =>
%%%
htmlSplit := .never
tag := "introduction"
%%%

The _Lean Language Reference_ is intended as a comprehensive, precise description of Lean.
It is first and foremost a reference work in which Lean users can look up detailed information, rather than a tutorial for new users.
At the moment, this reference manual is a public preview.
Many sections are still to be written.
For tutorials and learning materials, please visit [the Lean documentation page](https://lean-lang.org/documentation/).

This document describes version {versionString}[] of Lean.

# Lean
%%%
tag := "what-is-lean"
%%%


Lean is an *interactive theorem prover* based on dependent type theory, designed for use both in cutting-edge mathematics and in software verification.
Lean's core type theory is expressive enough to capture very complicated mathematical objects, but simple enough to admit independent implementations, reducing the risk of bugs that affect soundness.
The core type theory is implemented in a minimal {tech}[kernel] that does nothing other than check proof terms.
This core theory and kernel are supported by advanced automation, realized in {ref "tactics"}[an expressive tactic language].
Each tactic produces a term in the core type theory that is checked by the kernel, so bugs in tactics do not threaten the soundness of Lean as a whole.
Along with many other parts of Lean, the tactic language is user-extensible, so it can be built up to meet the needs of a given formalization project.
Tactics are written in Lean itself, and can be used immediately upon definition; rebuilding the prover or loading external modules is not required.

Lean is also a pure *functional programming language*, with features such as a run-time system based on reference counting that can efficiently work with packed array structures, multi-threading, and monadic {name}`IO`.
As befits a programming language, Lean is primarily implemented in itself, including the language server, build tool, {tech}[elaborator], and tactic system.
This very book is written in [Verso](https://github.com/leanprover/verso), a documentation authoring tool written in Lean.

Familiarity with Lean's programming features is valuable even for users whose primary interest is in writing proofs, because Lean programs are used to implement new tactics and proof automation.
Thus, this reference manual does not draw a barrier between the two aspects, but rather describes them together so they can shed light on one another.

## History
%%%
tag := "history-of-lean"
%%%

Leonardo de Moura launched the Lean project when he was at Microsoft Research in 2013, and Lean 0.1 was officially released on June 16, 2014.
The goal of the Lean project is to combine the high level of trust provided by a small, independently-implementable logical kernel with the convenience and automation of tools like SMT solvers, while scaling to large problems.
This vision still guides the development of Lean, as we invest in improved automation, improved performance, and user-friendliness; the trusted core proof checker is still minimal and independent implementations exist.

The initial versions of Lean were primarily configured as C++ libraries in which client code could carry out trustworthy proofs that were independently checkable.
In these early years, the design of Lean rapidly evolved towards traditional interactive provers, first with tactics written in Lua, and later with a dedicated front-end syntax.
January 20, 2017 saw the first release of the Lean 3.0 series.
Lean 3 achieved widespread adoption by mathematicians, and pioneered self-extensibility: tactics, notations, and top-level commands could all be defined in Lean itself.
The mathematics community built Mathlib, which at the end of Lean 3 had over one million lines of formalized mathematics, with all proofs mechanically checked.
The system itself, however, was still implemented in C++, which imposed limits on Lean's flexibility and made it more difficult to develop due to the diverse skills required.

Development of Lean 4 began in 2018, culminating in the 4.0 release on September 8, 2023.
Lean 4 represents an important milestone: as of version 4, Lean is self-hosted - approximately 90% of the code that implements Lean is itself written in Lean.
Lean 4's rich extension API provides users with the ability to adapt it to their needs, rather than relying on the core developers to add necessary features.
Additionally, self-hosting makes the development process much faster, so features and performance can be delivered more quickly; Lean 4 is faster and scales to larger problems than Lean 3.
Mathlib was successfully ported to Lean 4 in 2023 through a community effort supported by the Lean developers, and it has now grown to over 1.5 million lines.
Even though Mathlib has grown by 50%, Lean 4 checks it faster than Lean 3 could check its smaller library.
The development process for Lean 4 was approximately as long as that of all prior versions combined, and we are now delighted with its design—no further rewrites are planned.

Leonardo de Moura and his co-founder, Sebastian Ullrich, launched the Lean Focused Research Organization (FRO) nonprofit in July of 2023 within Convergent Research, with philanthropic support from the Simons Foundation International, the Alfred P. Sloan Foundation, and Richard Merkin.
The FRO currently has more than ten employees working to support the growth and scalability of Lean and the broader Lean community.


# Typographical Conventions
%%%
tag := "typographical-conventions"
%%%

This document makes use of a number of typographical and layout conventions to indicate various aspects of the information being presented.

## Lean Code
%%%
tag := "code-samples"
%%%


This document contains many Lean code examples.
They are formatted as follows:

````lean
def hello : IO Unit := IO.println "Hello, world!"
````

Compiler output (which may be errors, warnings, or just information) is shown both in the code and separately:

````lean (name := output) (error := true)
#eval s!"The answer is {2 + 2}"

theorem bogus : False := by sorry

example := Nat.succ "two"
````

Informative output, such as the result of {keywordOf Lean.Parser.Command.eval}`#eval`, is shown like this:
```leanOutput output (severity := information)
"The answer is 4"
```

Warnings are shown like this:
```leanOutput output (severity := warning)
declaration uses 'sorry'
```

Error messages are shown like this:
```leanOutput output (severity := error)
application type mismatch
  Nat.succ "two"
argument
  "two"
has type
  String : Type
but is expected to have type
  Nat : Type
```


The presence of tactic proof states is indicated by the presence of small lozenges that can be clicked to show the proof state, such as after {tactic}`rfl` below:
```lean
example : 2 + 2 = 4 := by rfl
```

:::tacticExample
Proof states may also be shown on their own.
When attempting to prove that {goal}`2 + 2 = 4`, the initial proof state is:
```pre
⊢ 2 + 2 = 4
```
After using {tacticStep}`rfl`, the resulting state is:
```post

```

```setup
skip
```
:::

Identifiers in code examples are hyperlinked to their documentation.

Examples of code with syntax errors are shown with an indicator of where the parser stopped, along with the error message:
```syntaxError intro
def f : Option Nat → Type
  | some 0 => Unit
  | => Option (f t)
  | none => Empty
```
```leanOutput intro
<example>:3:4: expected term
```

## Examples
%%%
tag := "example-boxes"
%%%


Illustrative examples are in callout boxes, as below:

::::keepEnv
:::example "Even Numbers"
This is an example of an example.

One way to define even numbers is via an inductive predicate:
```lean
inductive Even : Nat → Prop where
  | zero : Even 0
  | plusTwo : Even n → Even (n + 2)
```
:::
::::

## Technical Terminology
%%%
tag := "technical-terms"
%%%


{deftech}_Technical terminology_ refers to terms used in a very specific sense when writing technical material, such as this reference.
Uses of {tech}[technical terminology] are frequently hyperlinked to their definition sites, using links like this one.

## Constant, Syntax, and Tactic References
%%%
tag := "reference-boxes"
%%%


Definitions, inductive types, syntax formers, and tactics have specific descriptions.
These descriptions are marked as follows:

::::keepEnv
```lean
/--
Evenness: a number is even if it can be evenly divided by two.
-/
inductive Even : Nat → Prop where
  | /-- 0 is considered even here -/
    zero : Even 0
  | /-- If `n` is even, then so is `n + 2`. -/
    plusTwo : Even n → Even (n + 2)
```

{docstring Even}

::::
