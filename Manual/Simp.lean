import VersoManual

import Lean.Parser.Term

import Manual.Meta

open Verso.Genre Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "The Simplifier" =>
%%%
tag := "the-simplifier"
%%%

The simplifier is one of the most-used features of Lean.
It performs inside-out rewriting of terms based on a database of simplification rules.
The simplifier is highly configurable, and a number of tactics use it in different ways.

# Invoking the Simplifier


Lean's simplifier can be invoked in a variety of ways.
The most common patterns are captured in a set of tactics.
The {ref "simp-tactics"}[tactic reference] contains a complete list of simplification tactics.

Simplification tactics all contain `simp` in their name.
Aside from that, they are named according to a system of prefixes and suffixes that describe their functionality:

: `-!` suffix

  Sets the {name Lean.Meta.Simp.Config.autoUnfold}`autoUnfold` configuration option to `true`, causing the simplifier unfold all definitions

: `-?` suffix

  Causes the simplifier to keep track of which rules it employed during simplification and suggest a minimal {tech}[simp set] as an edit to the tactic script

: `-_arith` suffix

  Enables the use of linear arithmetic simplfication rules

: `d-` prefix

  Causes the simplifier to simplify only with rewrites that hold definitionally

: `-_all` suffix

  Causes the simplifier to repeatedly simplify all assumptions and the conclusion of the goal, taking as many hypotheses into account as possible, until no further simplification is possible

There are two further simplification tactics, {tactic}`simpa` and {tactic}`simpa!`, which are used to simultaneously simplify a goal and either a proof term or an assumption before discharging the goal.
This simultaneous simplification makes proofs more robust to changes in the {tech}[simp set].

## Parameters

The simplification tactics have the following grammar:

:::syntax tactic
```grammar
simp $[(config := $cfg)]? $[only]? $[ [ $[$e],* ] ]? $[at $[$h]*]?
```
:::

In other words, an invocation of a simplification tactic takes the following modifiers, in order, all of which are optional:
 * A configuration specifier, which should be an instance of {name}`Lean.Meta.Simp.Config` or {name}`Lean.Meta.DSimp.Config`, depending on whether the simplifier being invoked is a version of {tactic}`simp` or a version of {tactic}`dsimp`.
 * The {keywordOf Lean.Parser.Tactic.simp}`only` modifier excludes the default simp set, instead beginning with an empty simp set.
 * The lemma list adds or removes lemmas from the simp set. There are three ways to specify lemmas in the lemma list:
   * `*`, which adds all assumptions in the proof state to the simp set
   * `-` followed by a lemma, which removes the lemma from the simp set
   * A lemma specifier, consisting of the following in sequence:
      * An optional `↑` or `↓`, which determines whether to apply a lemma before or after entering a subterm {TODO}[Precisely describe what this means]
      * An optional `←`, which causes equational lemmas to be used from right to left rather than from left to right
      * A mandatory lemma, which can be a simp set name, a lemma name, or a term. {TODO}[What are the precise semantics of a term like `(· + ·)` there?]
 * A location specifier, preceded by {keywordOf Lean.Parser.Tactic.simp}`at`, which consists of a sequence of locations. Locations may be:

   - The name of an assumption, indicating that its type should be simplified
   - An asterisk `*`, indicating that all assumptions and the conclusion should be simplified
   - A turnstile `⊢`, indicating that the conclusion should be simplified

  By default, only the conclusion is simplified.

::::example "Location specifiers for {tactic}`simp`"
:::tacticExample
{goal show:=false}`∀ (p : Nat → Prop) (x : Nat) (h : p (x + 5 + 2)) (h' : p (3 + x + 9)), p (6 + x + 1)`
```setup
intro p x h h'
```

In this proof state,
```pre
p : Nat → Prop
x : Nat
h : p (x + 5 + 2)
h' : p (3 + x + 9)
⊢ p (6 + x + 1)
```

the tactic {tacticStep}`simp_arith` simplifies only the goal:

```post
p : Nat → Prop
x : Nat
h : p (x + 5 + 2)
h' : p (3 + x + 9)
⊢ p (x + 7)
```
:::

:::tacticExample
{goal show:=false}`∀ (p : Nat → Prop) (x : Nat) (h : p (x + 5 + 2)) (h' : p (3 + x + 9)), p (6 + x + 1)`
```setup
intro p x h h'
```
```pre (show := false)
p : Nat → Prop
x : Nat
h : p (x + 5 + 2)
h' : p (3 + x + 9)
⊢ p (6 + x + 1)
```

Invoking {tacticStep}`simp_arith at h` yields a goal in which the hypothesis `h` has been simplified:

```post
p : Nat → Prop
x : Nat
h' : p (3 + x + 9)
h : p (x + 7)
⊢ p (6 + x + 1)
```
:::

:::tacticExample
{goal show:=false}`∀ (p : Nat → Prop) (x : Nat) (h : p (x + 5 + 2)) (h' : p (3 + x + 9)), p (6 + x + 1)`
```setup
intro p x h h'
```
```pre (show := false)
p : Nat → Prop
x : Nat
h : p (x + 5 + 2)
h' : p (3 + x + 9)
⊢ p (6 + x + 1)
```

The conclusion can be additionally simplified by adding `⊢`, that is, {tacticStep}`simp_arith at h ⊢`:

```post
p : Nat → Prop
x : Nat
h' : p (3 + x + 9)
h : p (x + 7)
⊢ p (x + 7)
```
:::

:::tacticExample
{goal show:=false}`∀ (p : Nat → Prop) (x : Nat) (h : p (x + 5 + 2)) (h' : p (3 + x + 9)), p (6 + x + 1)`
```setup
intro p x h h'
```
```pre (show := false)
p : Nat → Prop
x : Nat
h : p (x + 5 + 2)
h' : p (3 + x + 9)
⊢ p (6 + x + 1)
```

Using {tacticStep}`simp_arith at *` simplifies all assumptions together with the conclusion:

```post
p : Nat → Prop
x : Nat
h : p (x + 7)
h' : p (x + 12)
⊢ p (x + 7)
```
:::
::::


# Rewrite Rules

The simplifier has three kinds of rewrite rules:

: Declarations to unfold

  The simplifier will only unfold {tech}[reducible] definitions by default. However, a rewrite rule can be added for any {tech}[semireducible] or {tech}[irreducible] definition that causes the simplifier to unfold it as well. When the simplifier is running in definitional mode ({tactic}`dsimp` and its variants), definition unfolding only replaces the defined name with its value; otherwise, it also uses the equational lemmas produced by the equation compiler.

: Equational lemmas

  The simplifier can treat equality proofs as rewrite rules, in which case the left side of the equality will be replaced with the right. These equational lemmas may have any number of parameters. The simplifier instantiates parameters to make the left side of the equality match the goal, and it performs a proof search to instantiate any additional parameters.

: Simplification procedures

  The simplifier supports simplification procedures, known as {deftech}_simprocs_, that use Lean metaprogramming to perform rewrites that can't be efficiently specified using equations. Lean includes simprocs for the most important operations on built-in types.


```lean (show := false)
-- Validate the above description of reducibility

@[irreducible]
def foo (x : α) := x

set_option allowUnsafeReducibility true in
@[semireducible]
def foo' (x : α) := x

@[reducible]
def foo'' (x : α) := x

/--
error: unsolved goals
α✝ : Type u_1
x y : α✝
⊢ x = y ∧ y = x
-/
#guard_msgs in
example : foo (x, y) = (y, x) := by
  simp [foo]

/-- error: simp made no progress -/
#guard_msgs in
example : foo (x, y) = (y, x) := by
  simp

/--
error: unsolved goals
α✝ : Type u_1
x y : α✝
⊢ x = y ∧ y = x
-/
#guard_msgs in
example : foo' (x, y) = (y, x) := by
  simp [foo']

/-- error: simp made no progress -/
#guard_msgs in
example : foo' (x, y) = (y, x) := by
  simp

/--
error: unsolved goals
α✝ : Type u_1
x y : α✝
⊢ x = y ∧ y = x
-/
#guard_msgs in
example : foo'' (x, y) = (y, x) := by
  simp [foo'']

/--
error: unsolved goals
α✝ : Type u_1
x y : α✝
⊢ x = y ∧ y = x
-/
#guard_msgs in
example : foo'' (x, y) = (y, x) := by
  simp

```

Due to {tech}[propositional extensionality], equational lemmas can rewrite propositions to simpler, logically equivalent propositions.
When the simplifier rewrites a proof goal to {lean}`True`, it automatically closes it.
As a special case of equational lemmas, propositions other than equality can be tagged as rewrite rules
They are preprocessed into rules that rewrite the proposition to {lean}`True`.

:::::example "Rewriting Propositions"
::::tacticExample

{goal show:=false}`∀(α β : Type) (w y : α) (x z : β), (w, x) = (y, z)`
```setup
intro α β w y x z
```

When asked to simplify an equality of pairs:
```pre
α β : Type
w y : α
x z : β
⊢ (w, x) = (y, z)
```

{tacticStep}`simp` yields a conjunction of equalities:

```post
α β : Type
w y : α
x z : β
⊢ w = y ∧ x = z
```

The default simp set contains {lean}`Prod.mk.injEq`, which shows the equivalence of the two statements:

```signature
Prod.mk.injEq.{u, v} {α : Type u} {β : Type v} (fst : α) (snd : β) :
  ∀ (fst_1 : α) (snd_1 : β),
    ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
```
::::
:::::


# Simp sets

A collection of rules used by the simplifier is called a {deftech}_simp set_.
A simp set is specified in terms of modifications from a _default simp set_.
These modifications can include adding rules, removing rules, or adding a set of rules.
The `only` modifier to the {tactic}`simp` tactic causes it to start with an empty simp set, rather than the default one.
Rules are added to the default simp set using the {attr}`simp` attribute.


:::TODO
Figure out exactly what `simp only` does, and document it here (it's not a no-op).
:::

:::TODO
Also describe putting expressions in the simp set rather than constant names
:::

:::planned
* simp?
* what's allowed in the square brackets

:::

:::syntax attr alias := Lean.Meta.simpExtension label:="attribute"
The {attr}`simp` attribute adds a declaration to the default simp set.
If the declaration is a definition, the definition is marked for unfolding; if it is a theorem, then the theorem is registered as a rewrite rule.

```grammar
simp
```


```grammar
simp ↑ $p?
```

```grammar
simp ↓ $p?
```

```lean (show := false)
-- Check above claim about default priority
/-- info: 1000 -/
#guard_msgs in
#eval eval_prio default
```
:::

Custom simp sets are created with {name Lean.Meta.registerSimpAttr}`registerSimpAttr`, which must be run in an {keywordOf Lean.Parser.Command.initialize}`initialize` block.{TODO}[xref]
As a side effect, it creates a new attribute with the same interface as {attr}`simp` that adds rules to the custom simp set.
The returned value is a {name Lean.Meta.SimpExtension}`SimpExtension`, which can be used to programmatically access the contents of the custom simp set.
The {tactic}`simp` tactics can be instructed to use the new simp set by including its attribute name in the rule list.

{docstring Lean.Meta.registerSimpAttr}

{docstring Lean.Meta.SimpExtension}



# Simp Normal Forms

The default {tech}[simp set] contains all the theorems and simplification procedures marked with the {attr}`simp` attribute.
The {deftech}_simp normal form_ of an expression is the result of applying the default simp set via the {tactic}`simp` tactic until no more rules can be applied.
When an expression is in simp normal form, it is as reduced as possible according to the default simp set, often making it easier to work with in proofs.

The {tactic}`simp` tactic *does not guarantee confluence*, which means that the simp normal form of an expression may depend on the order in which the elements of the default simp set are applied.
The order in which the rules are applied can be changed by assigning priorities when setting the {attr}`simp` attribute.

When designing a Lean library, it's important to think about what the appropriate simp normal form for the various combinations of the library's operators is.
This can serve as a guide when selecting which rules the library should add to the default simp set.
Even though simplification doesn't need to be confluent, striving for confluence is helpful because it makes the library more predictable and tends to reveal missing or poorly chosen.
The default simp set is as much a part of a library's interface as the type signatures of the constants that it exports.

Libraries should not add rules to the default simp set that don't mention at least one constant defined in the library.
Otherwise, importing a library could change the behavior of {tactic}`simp` for some unrelated library.
If your library relies on additional simplification rules for other libraries, please create a custom simp set and either instruct users to use it or provide a custom tactic.


# Terminal vs Non-Terminal Positions

To write maintainable proofs, avoid using {tactic}`simp` without {keywordOf Lean.Parser.Tactic.simp}`only` unless it closes the goal.
Such uses of {tactic}`simp` that do not close a goal are referred to as {deftech}_non-terminal simps_.
This is because additions to the default simp set may make {tactic}`simp` more powerful or just cause it to select a different sequence of rewrites and arrive at a different simp normal form.
When {keywordOf Lean.Parser.Tactic.simp}`only` is specified, additional lemmas will not affect that invocation of the tactic.
In practice, terminal uses of {tactic}`simp` are not nearly as likely to be broken by the addition of new simp lemmas, and when they are, it's easier to understand the issue and fix it.


# Configuring Simplification

{tactic}`simp` is primarily configured via a configuration parameter, passed as a named argument called `config`.

{docstring Lean.Meta.Simp.Config}

{docstring Lean.Meta.Simp.neutralConfig}

{docstring Lean.Meta.DSimp.Config}

## Options

Some global options affect {tactic}`simp`:

{optionDocs simprocs}

{optionDocs tactic.simp.trace}

{optionDocs linter.unnecessarySimpa}

# Simplification vs Rewriting

:::planned
A comparison of {tactic}`simp` and {tactic}`rw` and their rewriting strategies. Refer to internal Zulip thread where Leo lays it out.
:::
