/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Lean.MessageSeverity

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Interacting with Lean" =>
%%%
htmlSplit := .never
tag := "interaction"
%%%

Lean is designed for interactive use, rather than as a batch-mode system in which whole files are fed in and then translated to either object code or error messages.
Many programming languages designed for interactive use provide a {deftech}[REPL],{margin}[Short for “*R*ead-*E*val-*P*rint *L*oop”, because code is parsed (“read”), evaluated, and the result displayed, with this process repeated as many times as desired.] at which code can be input and tested, along with commands for loading source files, type checking terms, or querying the environment.
Lean's interactive features are based on a different paradigm.
Rather than a separate command prompt outside of the program, Lean provides {tech}[commands] for accomplishing the same tasks in the context of a source file.
By convention, commands that are intended for interactive use rather than as part of a durable code artifact are prefixed with {keyword}`#`.

:::TODO

How is the output displayed?

info, warning, error

:::

# Evaluating Terms
%%%
tag := "hash-eval"
%%%

The {keywordOf Lean.Parser.Command.eval}`#eval` command is used to run code as a program.
In particular, it is capable of executing {lean}`IO` actions, it uses a call-by-value evaluation strategy, {ref "partial-unsafe"}[`partial` functions are executed], and both types and proofs are erased.
Use {keywordOf Lean.reduceCmd}`#reduce` to instead reduce terms using the reduction rules that are part of {tech}[definitional equality].

:::syntax command (title := "Evaluating Terms")

```grammar
#eval $t
```

```grammar
#eval! $t
```

{includeDocstring Lean.Parser.Command.eval}

:::

{keywordOf Lean.Parser.Command.eval}`#eval` always {tech}[elaborates] and compiles the provided term.
It then checks whether the term transitively depends on any uses of {lean}`sorry`, in which case evaluation is terminated unless the command was invoked as {keywordOf Lean.Parser.Command.eval}`#eval!`.
This is because compiled code may rely on compile-time invariants (such as array lookups being in-bounds) that are ensured by proofs of suitable statements, and running code that contains incomplete proofs (or uses of {lean}`sorry` that “prove” incorrect statements) can cause Lean itself to crash.

```lean (show := false)
section
variable (m : Type → Type)
open Lean.Elab.Command (CommandElabM)
```

:::paragraph

The way the code is run depends on its type:

 * If the type is in the {lean}`IO` monad, then it is executed in a context where {tech}[standard output] and {tech}[standard error] are captured and redirected to the Lean {tech}[message log].
   If the returned value's type is not {lean}`Unit`, then it is displayed as if it were the result of a non-monadic expression.
 * If the type is in one of the internal Lean metaprogramming monads ({name Lean.Elab.Command.CommandElabM}`CommandElabM`, {name Lean.Elab.Term.TermElabM}`TermElabM`, {name Lean.MetaM}`MetaM`, or {name Lean.CoreM}`CoreM`), then it is run in the current context.
    For example, the environment will contain the definitions that are in scope where {keywordOf Lean.Parser.Command.eval}`#eval` is invoked.
    As with {name}`IO`, the resulting value is displayed as if it were the result of a non-monadic expression.
 * If the type is in some other monad {lean}`m`, and there is a {lean}`MonadLiftT m CommandElabM` or {lean}`MonadEvalT m CommandElabM` instance, then {name}`MonadLiftT.monadLift` or {name}`MonadEvalT.monadEval` is used to transform the monad into one that may be run with {keywordOf Lean.Parser.Command.eval}`#eval`, after which it is run as usual.
 * If the term's type is not in any of the supported monads, then it is treated as a pure value.
  The compiled code is run, and the result is displayed.

Auxiliary definitions or other environment modifications that result from elaborating the term in {keywordOf Lean.Parser.Command.eval}`#eval` are discarded.
If the term is an action in a metaprogramming monad, then changes made to the environment by the running the monadic action are preserved.
:::

```lean (show := false)
end
```

Results are displayed using a {name Lean.ToExpr}`ToExpr`, {name}`ToString`, or {name}`Repr` instance, if they exist.
If not, and {option}`eval.derive.repr` is {lean}`true`, Lean attempts to derive a suitable {name}`Repr` instance.
It is an error if no suitable instance can be found or derived.
Setting {option}`eval.pp` to {lean}`false` disables the use of {name Lean.ToExpr}`ToExpr` instances by {keywordOf Lean.Parser.Command.eval}`#eval`.

:::example "Displaying Output"

{keywordOf Lean.Parser.Command.eval}`#eval` cannot display functions:
```lean (name := funEval) (error := true)
#eval fun x => x + 1
```
```leanOutput funEval
could not synthesize a 'ToExpr', 'Repr', or 'ToString' instance for type
  Nat → Nat
```

It is capable of deriving instances to display output that has no {name}`ToString` or {name}`Repr` instance:

```lean (name := quadEval)
inductive Quadrant where
  | nw | sw | se | ne

#eval Quadrant.nw
```
```leanOutput quadEval
Quadrant.nw
```

The derived instance is not saved.
Disabling {option}`eval.derive.repr` causes {keywordOf Lean.Parser.Command.eval}`#eval` to fail:

```lean (name := quadEval2) (error := true)
set_option eval.derive.repr false
#eval Quadrant.nw
```
```leanOutput quadEval2
could not synthesize a 'ToExpr', 'Repr', or 'ToString' instance for type
  Quadrant
```

:::

{optionDocs eval.pp}

{optionDocs eval.type}

{optionDocs eval.derive.repr}

Monads can be given the ability to execute in {keywordOf Lean.Parser.Command.eval}`#eval` by defining a suitable {lean}`MonadLift`{margin}[{lean}`MonadLift` is described in {ref "lifting-monads"}[the section on lifting monads.]] or {lean}`MonadEval` instance.
Just as {name}`MonadLiftT` is the transitive closure of {name}`MonadLift` instances, {name}`MonadEvalT` is the transitive closure of {name}`MonadEval` instances; like {name}`MonadLiftT` users should not define additional instances of {name}`MonadEvalT` directly.

{docstring MonadEval}

{docstring MonadEvalT}

# Reducing Terms
%%%
tag := "hash-reduce"
%%%

The {keywordOf Lean.reduceCmd}`#reduce` command repeatedly applies reductions to a term until no further reductions are possible.
Reductions are performed under binders, but to avoid unexpected slowdowns, proofs and types are skipped unless the corresponding options to {keywordOf Lean.reduceCmd}`#reduce` are enabled.
Unlike {keywordOf Lean.Parser.Command.eval}`#eval` command, reduction cannot have side effects and the result is displayed as a term rather than via a {name}`ToString` or {name}`Repr` instance.
Generally speaking, {keywordOf Lean.reduceCmd}`#reduce` is primarily useful for diagnosing issues with definitional equality and proof terms, while {keywordOf Lean.Parser.Command.eval}`#eval` is more suitable for computing the value of a term.

:::syntax command (title := "Reducing Terms")
```grammar
#reduce $[(proofs := true)]? $[(types := true)]? $t
```

{includeDocstring Lean.reduceCmd}

:::

:::example "Reducing Functions"

Reducing a term results in its normal form in Lean's logic.
In some cases, this normal form is short and resembles a term that a person might write:
```lean (name := plusOne)
#reduce (fun x => x + 1)
```
```leanOutput plusOne
fun x => x.succ
```

In other cases, the details of {ref "elab-as-course-of-values"}[the elaboration of functions] such as addition to Lean's core logic are exposed:
```lean (name := onePlus)
#reduce (fun x => 1 + x)
```
```leanOutput onePlus
fun x => (Nat.rec ⟨fun x => x, PUnit.unit⟩ (fun n n_ih => ⟨fun x => (n_ih.1 x).succ, n_ih⟩) x).1 1
```

:::

# Checking Types
%%%
tag := "hash-check"
%%%

:::syntax command (title := "Checking Types")

{keyword}`#check` can be used to elaborate a term and check its type.

```grammar
#check $t
```

If the provided term is an identifier that is the name of a global constant, then {keyword}`#check` prints its signature.
Otherwise, the term is elaborated as a Lean term and its type is printed.
Elaboration may succeed even if the type contains metavariables.

:::



:::example "{keyword}`#check` and Underdetermined Types"
In this example, the type of the lists' elements is not determined, so the type contains a metavariable:
```lean (name := singletonList)
#check fun x => [x]
```
```leanOutput singletonList
fun x => [x] : ?m.9 → List ?m.9
```
:::

:::syntax command (title := "Testing Type Errors")
```grammar
#check_failure $t
```
 * Succeeds if the other fails
 * Still prints the term (hovers etc)
:::


:::example "Checking for Type Errors"
```lean (name := oneOne)
#check_failure "one" + 1
```
```leanOutput oneOne
failed to synthesize
  HAdd String Nat ?m.32
Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
:::


# Querying the Context
%%%
tag := "hash-print"
%%%

The {keyword}`#print` family of commands are used to query Lean for information about definitions.

:::syntax command (title := "Printing Definitions")
```grammar
#print $t:ident
```
:::

:::syntax command (title := "Printing Strings")
```grammar
#print $s:str
```
:::


:::syntax command (title := "Printing Axioms")
```grammar
#print axioms $t
```
:::

:::syntax command (title := "Printing Equations")
```grammar
#print equations $t
```
```grammar
#print eqns $t
```
:::

:::example "Printing Equations"

```lean (name := intersperse_eqns)
def intersperse (x : α) : List α → List α
  | y :: z :: zs => y :: x :: intersperse x (z :: zs)
  | xs => xs

#print equations intersperse
```
```leanOutput intersperse_eqns
equations:
theorem intersperse.eq_1.{u_1} : ∀ {α : Type u_1} (x y z : α) (zs : List α),
  intersperse x (y :: z :: zs) = y :: x :: intersperse x (z :: zs)
theorem intersperse.eq_2.{u_1} : ∀ {α : Type u_1} (x : α) (x_1 : List α),
  (∀ (y z : α) (zs : List α), x_1 = y :: z :: zs → False) → intersperse x x_1 = x_1
```

It does not print the defining equation, nor the unfolding equation:
```lean (name := intersperse_eq_def)
#check intersperse.eq_def
```
```leanOutput intersperse_eq_def
intersperse.eq_def.{u_1} {α : Type u_1} (x : α) (x✝ : List α) :
  intersperse x x✝ =
    match x✝ with
    | y :: z :: zs => y :: x :: intersperse x (z :: zs)
    | xs => xs
```

```lean (name := intersperse_eq_unfold)
#check intersperse.eq_unfold
```
```leanOutput intersperse_eq_unfold
intersperse.eq_unfold.{u_1} :
  @intersperse = fun {α} x x_1 =>
    match x_1 with
    | y :: z :: zs => y :: x :: intersperse x (z :: zs)
    | xs => xs
```

:::

:::syntax command (title := "Scope Information")

{includeDocstring Lean.Parser.Command.where}

```grammar
#where
```
:::

:::example "Scope Information"

```lean (fresh := true) (name := scopeInfo)
section
open Nat

namespace A
variable (n : Nat)
namespace B

open List
set_option pp.funBinderTypes true

#where

end A.B
end
```
```leanOutput scopeInfo
namespace A.B

open Nat List

variable (n : Nat)

set_option pp.funBinderTypes true
```

:::

:::syntax command (title := "Checking the Lean Version")

{includeDocstring Lean.Parser.Command.version}

```grammar
#version
```
:::


# Tests
%%%
tag := "hash-guard_msgs"
%%%

:::syntax command (title := "Documenting Expected Output")
```grammar
$[$_:docComment]?
#guard_msgs $[($_,*)]? in
$c:command
```
:::

:::syntax Lean.guardMsgsSpecElt (title := "Specifying `#guard_msgs Behavior`") (open := false)
```grammar
$_:guardMsgsFilter
```
```grammar
whitespace := $_
```
```grammar
ordering := $_
```

:::

:::syntax Lean.guardMsgsFilter (title := "Output Selection for `#guard_msgs`") (open := false)
```grammar
$[drop]? all
```
```grammar
$[drop]? info
```
```grammar
$[drop]? warning
```
```grammar
$[drop]? error
```

:::


:::syntax Lean.guardMsgsWhitespaceArg (title := "Whitespace Comparison for `#guard_msgs`") (open := false)
```grammar
exact
```
```grammar
lax
```
```grammar
normalized
```

:::



{optionDocs guard_msgs.diff}
