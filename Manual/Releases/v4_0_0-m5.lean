/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.0.0-m5 (2022-08-22)" =>
%%%
tag := "release-v4.0.0-m5"
file := "v4.0.0-m5"
%%%

````markdown
This is the fifth milestone release of Lean 4. It contains many improvements and many new features.
 We had  1495 commits since the last milestone.

Contributors:
```
   885  Leonardo de Moura
   310  Sebastian Ullrich
    69  E.W.Ayers
    66  Wojciech Nawrocki
    49  Gabriel Ebner
    38  Mario Carneiro
    22  larsk21
    10  tydeu
     6  Ed Ayers
     6  Mariana Alanis
     4  Chris Lovett
     3  Jannis Limperg
     2  François G. Dorais
     2  Henrik Böving
     2  Jakob von Raumer
     2  Scott Morrison
     2  Siddharth
     1  Andrés Goens
     1  Arthur Paulino
     1  Connor Baker
     1  Joscha
     1  KaseQuark
     1  Lars
     1  Mac
     1  Marcus Rossel
     1  Patrick Massot
     1  Siddharth Bhat
     1  Timo
     1  Vincent de Haan
     1  William Blake
     1  Yuri de Wit
     1  ammkrn
     1  asdasd1dsadsa
     1  kzvi
```



* Update Lake to v4.0.0. See the [v4.0.0 release notes](https://github.com/leanprover/lake/releases/tag/v4.0.0) for detailed changes.

* Mutual declarations in different namespaces are now supported. Example:
  ```lean
  mutual
    def Foo.boo (x : Nat) :=
      match x with
      | 0 => 1
      | x + 1 => 2*Boo.bla x

    def Boo.bla (x : Nat) :=
      match x with
      | 0 => 2
      | x+1 => 3*Foo.boo x
  end
  ```
  A `namespace` is automatically created for the common prefix. Example:
  ```lean
  mutual
    def Tst.Foo.boo (x : Nat) := ...
    def Tst.Boo.bla (x : Nat) := ...
  end
  ```
  expands to
  ```lean
  namespace Tst
  mutual
    def Foo.boo (x : Nat) := ...
    def Boo.bla (x : Nat) := ...
  end
  end Tst
  ```

* Allow users to install their own `deriving` handlers for existing type classes.
  See example at [Simple.lean](https://github.com/leanprover/lean4/blob/master/tests/pkg/deriving/UserDeriving/Simple.lean).

* Add tactic `congr (num)?`. See doc string for additional details.

* [Missing doc linter](https://github.com/leanprover/lean4/pull/1390)

* `match`-syntax notation now checks for unused alternatives. See issue [#1371](https://github.com/leanprover/lean4/issues/1371).

* Auto-completion for structure instance fields. Example:
  ```lean
  example : Nat × Nat := {
    f -- HERE
  }
  ```
  `fst` now appears in the list of auto-completion suggestions.

* Auto-completion for dotted identifier notation. Example:
  ```lean
  example : Nat :=
    .su -- HERE
  ```
  `succ` now appears in the list of auto-completion suggestions.

* `nat_lit` is not needed anymore when declaring `OfNat` instances. See issues [#1389](https://github.com/leanprover/lean4/issues/1389) and [#875](https://github.com/leanprover/lean4/issues/875). Example:
  ```lean
  inductive Bit where
    | zero
    | one

  instance inst0 : OfNat Bit 0 where
    ofNat := Bit.zero

  instance : OfNat Bit 1 where
    ofNat := Bit.one

  example : Bit := 0
  example : Bit := 1
  ```

* Add `[elabAsElim]` attribute (it is called `elab_as_eliminator` in Lean 3). Motivation: simplify the Mathlib port to Lean 4.

* `Trans` type class now accepts relations in `Type u`. See this [Zulip issue](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Calc.20mode/near/291214574).

* Accept unescaped keywords as inductive constructor names. Escaping can often be avoided at use sites via dot notation.
  ```lean
  inductive MyExpr
    | let : ...

  def f : MyExpr → MyExpr
    | .let ... => .let ...
  ```

* Throw an error message at parametric local instances such as `[Nat -> Decidable p]`. The type class resolution procedure
  cannot use this kind of local instance because the parameter does not have a forward dependency.
  This check can be disabled using `set_option checkBinderAnnotations false`.

* Add option `pp.showLetValues`. When set to `false`, the info view hides the value of `let`-variables in a goal.
  By default, it is `true` when visualizing tactic goals, and `false` otherwise.
  See [issue #1345](https://github.com/leanprover/lean4/issues/1345) for additional details.

* Add option `warningAsError`. When set to true, warning messages are treated as errors.

* Support dotted notation and named arguments in patterns. Example:
  ```lean
  def getForallBinderType (e : Expr) : Expr :=
    match e with
    | .forallE (binderType := type) .. => type
    | _ => panic! "forall expected"
  ```

* "jump-to-definition" now works for function names embedded in the following attributes
  `@[implementedBy funName]`, `@[tactic parserName]`, `@[termElab parserName]`, `@[commandElab parserName]`,
  `@[builtinTactic parserName]`, `@[builtinTermElab parserName]`, and `@[builtinCommandElab parserName]`.
   See [issue #1350](https://github.com/leanprover/lean4/issues/1350).

* Improve `MVarId` methods discoverability. See [issue #1346](https://github.com/leanprover/lean4/issues/1346).
  We still have to add similar methods for `FVarId`, `LVarId`, `Expr`, and other objects.
  Many existing methods have been marked as deprecated.

* Add attribute `[deprecated]` for marking deprecated declarations. Examples:
  ```lean
  def g (x : Nat) := x + 1

  -- Whenever `f` is used, a warning message is generated suggesting to use `g` instead.
  @[deprecated g]
  def f (x : Nat) := x + 1

  #check f 0 -- warning: `f` has been deprecated, use `g` instead

  -- Whenever `h` is used, a warning message is generated.
  @[deprecated]
  def h (x : Nat) := x + 1

  #check h 0 -- warning: `h` has been deprecated
  ```

* Add type `LevelMVarId` (and abbreviation `LMVarId`) for universe level metavariable ids.
  Motivation: prevent meta-programmers from mixing up universe and expression metavariable ids.

* Improve `calc` term and tactic. See [issue #1342](https://github.com/leanprover/lean4/issues/1342).

* [Relaxed antiquotation parsing](https://github.com/leanprover/lean4/pull/1272) further reduces the need for explicit `$x:p` antiquotation kind annotations.

* Add support for computed fields in inductives. Example:
  ```lean
  inductive Exp
    | var (i : Nat)
    | app (a b : Exp)
  with
    @[computedField] hash : Exp → Nat
      | .var i => i
      | .app a b => a.hash * b.hash + 1
  ```
  The result of the `Exp.hash` function is then stored as an extra "computed" field in the `.var` and `.app` constructors;
  `Exp.hash` accesses this field and thus runs in constant time (even on dag-like values).

* Update `a[i]` notation. It is now based on the typeclass
  ```lean
  class GetElem (cont : Type u) (idx : Type v) (elem : outParam (Type w)) (dom : outParam (cont → idx → Prop)) where
    getElem (xs : cont) (i : idx) (h : dom xs i) : Elem
  ```
  The notation `a[i]` is now defined as follows
  ```lean
  macro:max x:term noWs "[" i:term "]" : term => `(getElem $x $i (by get_elem_tactic))
  ```
  The proof that `i` is a valid index is synthesized using the tactic `get_elem_tactic`.
  For example, the type `Array α` has the following instances
  ```lean
  instance : GetElem (Array α) Nat α fun xs i => LT.lt i xs.size where ...
  instance : GetElem (Array α) USize α fun xs i => LT.lt i.toNat xs.size where ...
  ```
  You can use the notation `a[i]'h` to provide the proof manually.
  Two other notations were introduced: `a[i]!` and `a[i]?`, For `a[i]!`, a panic error message is produced at
  runtime if `i` is not a valid index. `a[i]?` has type `Option α`, and `a[i]?` evaluates to `none` if the
  index `i` is not valid.
  The three new notations are defined as follows:
  ```lean
  @[inline] def getElem' [GetElem cont idx elem dom] (xs : cont) (i : idx) (h : dom xs i) : elem :=
  getElem xs i h

  @[inline] def getElem! [GetElem cont idx elem dom] [Inhabited elem] (xs : cont) (i : idx) [Decidable (dom xs i)] : elem :=
    if h : _ then getElem xs i h else panic! "index out of bounds"

  @[inline] def getElem? [GetElem cont idx elem dom] (xs : cont) (i : idx) [Decidable (dom xs i)] : Option elem :=
    if h : _ then some (getElem xs i h) else none

  macro:max x:term noWs "[" i:term "]" noWs "?" : term => `(getElem? $x $i)
  macro:max x:term noWs "[" i:term "]" noWs "!" : term => `(getElem! $x $i)
  macro x:term noWs "[" i:term "]'" h:term:max : term => `(getElem' $x $i $h)
  ```
  See discussion on [Zulip](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/String.2EgetOp/near/287855425).
  Examples:
  ```lean
  example (a : Array Int) (i : Nat) : Int :=
    a[i] -- Error: failed to prove index is valid ...

  example (a : Array Int) (i : Nat) (h : i < a.size) : Int :=
    a[i] -- Ok

  example (a : Array Int) (i : Nat) : Int :=
    a[i]! -- Ok

  example (a : Array Int) (i : Nat) : Option Int :=
    a[i]? -- Ok

  example (a : Array Int) (h : a.size = 2) : Int :=
    a[0]'(by rw [h]; decide) -- Ok

  example (a : Array Int) (h : a.size = 2) : Int :=
    have : 0 < a.size := by rw [h]; decide
    have : 1 < a.size := by rw [h]; decide
    a[0] + a[1] -- Ok

  example (a : Array Int) (i : USize) (h : i.toNat < a.size) : Int :=
    a[i] -- Ok
  ```
  The `get_elem_tactic` is defined as
  ```lean
  macro "get_elem_tactic" : tactic =>
    `(first
      | get_elem_tactic_trivial
      | fail "failed to prove index is valid, ..."
     )
  ```
  The `get_elem_tactic_trivial` auxiliary tactic can be extended using `macro_rules`. By default, it tries `trivial`, `simp_arith`, and a special case for `Fin`. In the future, it will also try `linarith`.
  You can extend `get_elem_tactic_trivial` using `my_tactic` as follows
  ```lean
  macro_rules
  | `(tactic| get_elem_tactic_trivial) => `(tactic| my_tactic)
  ```
  Note that `Idx`'s type in `GetElem` does not depend on `Cont`. So, you cannot write the instance `instance : GetElem (Array α) (Fin ??) α fun xs i => ...`, but the Lean library comes equipped with the following auxiliary instance:
  ```lean
  instance [GetElem cont Nat elem dom] : GetElem cont (Fin n) elem fun xs i => dom xs i where
    getElem xs i h := getElem xs i.1 h
  ```
  and helper tactic
  ```lean
  macro_rules
  | `(tactic| get_elem_tactic_trivial) => `(tactic| apply Fin.val_lt_of_le; get_elem_tactic_trivial; done)
  ```
  Example:
  ```lean
  example (a : Array Nat) (i : Fin a.size) :=
    a[i] -- Ok

  example (a : Array Nat) (h : n ≤ a.size) (i : Fin n) :=
    a[i] -- Ok
  ```

* Better support for qualified names in recursive declarations. The following is now supported:
  ```lean
  namespace Nat
    def fact : Nat → Nat
    | 0 => 1
    | n+1 => (n+1) * Nat.fact n
  end Nat
  ```

* Add support for `CommandElabM` monad at `#eval`. Example:
  ```lean
  import Lean

  open Lean Elab Command

  #eval do
    let id := mkIdent `foo
    elabCommand (← `(def $id := 10))

  #eval foo -- 10
  ```

* Try to elaborate `do` notation even if the expected type is not available. We still delay elaboration when the expected type
  is not available. This change is particularly useful when writing examples such as
  ```lean
  #eval do
    IO.println "hello"
    IO.println "world"
  ```
  That is, we don't have to use the idiom `#eval show IO _ from do ...` anymore.
  Note that auto monadic lifting is less effective when the expected type is not available.
  Monadic polymorphic functions (e.g., `ST.Ref.get`) also require the expected type.

* On Linux, panics now print a backtrace by default, which can be disabled by setting the environment variable `LEAN_BACKTRACE` to `0`.
  Other platforms are TBD.

* The `group(·)` `syntax` combinator is now introduced automatically where necessary, such as when using multiple parsers inside `(...)+`.

* Add ["Typed Macros"](https://github.com/leanprover/lean4/pull/1251): syntax trees produced and accepted by syntax antiquotations now remember their syntax kinds, preventing accidental production of ill-formed syntax trees and reducing the need for explicit `:kind` antiquotation annotations. See PR for details.

* Aliases of protected definitions are protected too. Example:
  ```lean
  protected def Nat.double (x : Nat) := 2*x

  namespace Ex
  export Nat (double) -- Add alias Ex.double for Nat.double
  end Ex

  open Ex
  #check Ex.double -- Ok
  #check double -- Error, `Ex.double` is alias for `Nat.double` which is protected
  ```

* Use `IO.getRandomBytes` to initialize random seed for `IO.rand`. See discussion at [this PR](https://github.com/leanprover/lean4-samples/pull/2).

* Improve dot notation and aliases interaction. See discussion on [Zulip](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Namespace-based.20overloading.20does.20not.20find.20exports/near/282946185) for additional details.
  Example:
  ```lean
  def Set (α : Type) := α → Prop
  def Set.union (s₁ s₂ : Set α) : Set α := fun a => s₁ a ∨ s₂ a
  def FinSet (n : Nat) := Fin n → Prop

  namespace FinSet
    export Set (union) -- FinSet.union is now an alias for `Set.union`
  end FinSet

  example (x y : FinSet 10) : FinSet 10 :=
    x.union y -- Works
  ```

* `ext` and `enter` conv tactics can now go inside let-declarations. Example:
  ```lean
  example (g : Nat → Nat) (y : Nat) (h : let x := y + 1; g (0+x) = x) : g (y + 1) = y + 1 := by
    conv at h => enter [x, 1, 1]; rw [Nat.zero_add]
    /-
      g : Nat → Nat
      y : Nat
      h : let x := y + 1;
          g x = x
      ⊢ g (y + 1) = y + 1
    -/
    exact h
  ```

* Add `zeta` conv tactic to expand let-declarations. Example:
  ```lean
  example (h : let x := y + 1; 0 + x = y) : False := by
    conv at h => zeta; rw [Nat.zero_add]
    /-
      y : Nat
      h : y + 1 = y
      ⊢ False
    -/
    simp_arith at h
  ```

* Improve namespace resolution. See issue [#1224](https://github.com/leanprover/lean4/issues/1224). Example:
  ```lean
  import Lean
  open Lean Parser Elab
  open Tactic -- now opens both `Lean.Parser.Tactic` and `Lean.Elab.Tactic`
  ```

* Rename `constant` command to `opaque`. See discussion at [Zulip](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/What.20is.20.60opaque.60.3F/near/284926171).

* Extend `induction` and `cases` syntax: multiple left-hand-sides in a single alternative. This extension is very similar to the one implemented for `match` expressions. Examples:
  ```lean
  inductive Foo where
    | mk1 (x : Nat) | mk2 (x : Nat) | mk3

  def f (v : Foo) :=
    match v with
    | .mk1 x => x + 1
    | .mk2 x => 2*x + 1
    | .mk3   => 1

  theorem f_gt_zero : f v > 0 := by
    cases v with
    | mk1 x | mk2 x => simp_arith!  -- New feature used here!
    | mk3 => decide
  ```

* [`let/if` indentation in `do` blocks in now supported.](https://github.com/leanprover/lean4/issues/1120)

* Add unnamed antiquotation `$_` for use in syntax quotation patterns.

* [Add unused variables linter](https://github.com/leanprover/lean4/pull/1159). Feedback welcome!

* Lean now generates an error if the body of a declaration body contains a universe parameter that does not occur in the declaration type, nor is an explicit parameter.
  Examples:
  ```lean
  /-
  The following declaration now produces an error because `PUnit` is universe polymorphic,
  but the universe parameter does not occur in the function type `Nat → Nat`
  -/
  def f (n : Nat) : Nat :=
    let aux (_ : PUnit) : Nat := n + 1
    aux ⟨⟩

  /-
  The following declaration is accepted because the universe parameter was explicitly provided in the
  function signature.
  -/
  def g.{u} (n : Nat) : Nat :=
    let aux (_ : PUnit.{u}) : Nat := n + 1
    aux ⟨⟩
  ```

* Add `subst_vars` tactic.

* [Fix `autoParam` in structure fields lost in multiple inheritance.](https://github.com/leanprover/lean4/issues/1158).

* Add `[eliminator]` attribute. It allows users to specify default recursor/eliminators for the `induction` and `cases` tactics.
  It is an alternative for the `using` notation. Example:
  ```lean
  @[eliminator] protected def recDiag {motive : Nat → Nat → Sort u}
      (zero_zero : motive 0 0)
      (succ_zero : (x : Nat) → motive x 0 → motive (x + 1) 0)
      (zero_succ : (y : Nat) → motive 0 y → motive 0 (y + 1))
      (succ_succ : (x y : Nat) → motive x y → motive (x + 1) (y + 1))
      (x y : Nat) :  motive x y :=
    let rec go : (x y : Nat) → motive x y
      | 0,     0 => zero_zero
      | x+1, 0   => succ_zero x (go x 0)
      | 0,   y+1 => zero_succ y (go 0 y)
      | x+1, y+1 => succ_succ x y (go x y)
    go x y
  termination_by go x y => (x, y)

  def f (x y : Nat) :=
    match x, y with
    | 0,   0   => 1
    | x+1, 0   => f x 0
    | 0,   y+1 => f 0 y
    | x+1, y+1 => f x y
  termination_by f x y => (x, y)

  example (x y : Nat) : f x y > 0 := by
    induction x, y <;> simp [f, *]
  ```

* Add support for `casesOn` applications to structural and well-founded recursion modules.
  This feature is useful when writing definitions using tactics. Example:
  ```lean
  inductive Foo where
    | a | b | c
    | pair: Foo × Foo → Foo

  def Foo.deq (a b : Foo) : Decidable (a = b) := by
    cases a <;> cases b
    any_goals apply isFalse Foo.noConfusion
    any_goals apply isTrue rfl
    case pair a b =>
      let (a₁, a₂) := a
      let (b₁, b₂) := b
      exact match deq a₁ b₁, deq a₂ b₂ with
      | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁,h₂])
      | isFalse h₁, _ => isFalse (fun h => by cases h; cases (h₁ rfl))
      | _, isFalse h₂ => isFalse (fun h => by cases h; cases (h₂ rfl))
  ```

* `Option` is again a monad. The auxiliary type `OptionM` has been removed. See [Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Do.20we.20still.20need.20OptionM.3F/near/279761084).

* Improve `split` tactic. It used to fail on `match` expressions of the form `match h : e with ...` where `e` is not a free variable.
  The failure used to occur during generalization.


* New encoding for `match`-expressions that use the `h :` notation for discriminants. The information is not lost during delaboration,
  and it is the foundation for a better `split` tactic. at delaboration time. Example:
  ```lean
  #print Nat.decEq
  /-
  protected def Nat.decEq : (n m : Nat) → Decidable (n = m) :=
  fun n m =>
    match h : Nat.beq n m with
    | true => isTrue (_ : n = m)
    | false => isFalse (_ : ¬n = m)
  -/
  ```

* `exists` tactic is now takes a comma separated list of terms.

* Add `dsimp` and `dsimp!` tactics. They guarantee the result term is definitionally equal, and only apply
  `rfl`-theorems.

* Fix binder information for `match` patterns that use definitions tagged with `[matchPattern]` (e.g., `Nat.add`).
  We now have proper binder information for the variable `y` in the following example.
  ```lean
  def f (x : Nat) : Nat :=
    match x with
    | 0 => 1
    | y + 1 => y
  ```

* (Fix) the default value for structure fields may now depend on the structure parameters. Example:
  ```lean
  structure Something (i: Nat) where
  n1: Nat := 1
  n2: Nat := 1 + i

  def s : Something 10 := {}
  example : s.n2 = 11 := rfl
  ```

* Apply `rfl` theorems at the `dsimp` auxiliary method used by `simp`. `dsimp` can be used anywhere in an expression
  because it preserves definitional equality.

* Refine auto bound implicit feature. It does not consider anymore unbound variables that have the same
  name of a declaration being defined. Example:
  ```lean
  def f : f → Bool := -- Error at second `f`
    fun _ => true

  inductive Foo : List Foo → Type -- Error at second `Foo`
    | x : Foo []
  ```
  Before this refinement, the declarations above would be accepted and the
  second `f` and `Foo` would be treated as auto implicit variables. That is,
  `f : {f : Sort u} → f → Bool`, and
  `Foo : {Foo : Type u} → List Foo → Type`.


* Fix syntax highlighting for recursive declarations. Example
  ```lean
  inductive List (α : Type u) where
    | nil : List α  -- `List` is not highlighted as a variable anymore
    | cons (head : α) (tail : List α) : List α

  def List.map (f : α → β) : List α → List β
    | []    => []
    | a::as => f a :: map f as -- `map` is not highlighted as a variable anymore
  ```
* Add `autoUnfold` option to `Lean.Meta.Simp.Config`, and the following macros
  - `simp!` for `simp (config := { autoUnfold := true })`
  - `simp_arith!` for `simp (config := { autoUnfold := true, arith := true })`
  - `simp_all!` for `simp_all (config := { autoUnfold := true })`
  - `simp_all_arith!` for `simp_all (config := { autoUnfold := true, arith := true })`

  When the `autoUnfold` is set to true, `simp` tries to unfold the following kinds of definition
  - Recursive definitions defined by structural recursion.
  - Non-recursive definitions where the body is a `match`-expression. This
    kind of definition is only unfolded if the `match` can be reduced.
  Example:
  ```lean
  def append (as bs : List α) : List α :=
    match as with
    | [] => bs
    | a :: as => a :: append as bs

  theorem append_nil (as : List α) : append as [] = as := by
    induction as <;> simp_all!

  theorem append_assoc (as bs cs : List α) : append (append as bs) cs = append as (append bs cs) := by
    induction as <;> simp_all!
  ```

* Add `save` tactic for creating checkpoints more conveniently. Example:
  ```lean
  example : <some-proposition> := by
    tac_1
    tac_2
    save
    tac_3
    ...
  ```
  is equivalent to
  ```lean
  example : <some-proposition> := by
    checkpoint
      tac_1
      tac_2
    tac_3
    ...
  ```

* Remove support for `{}` annotation from inductive datatype constructors. This annotation was barely used, and we can control the binder information for parameter bindings using the new inductive family indices to parameter promotion. Example: the following declaration using `{}`
  ```lean
  inductive LE' (n : Nat) : Nat → Prop where
    | refl {} : LE' n n -- Want `n` to be explicit
    | succ  : LE' n m → LE' n (m+1)
  ```
  can now be written as
  ```lean
  inductive LE' : Nat → Nat → Prop where
    | refl (n : Nat) : LE' n n
    | succ : LE' n m → LE' n (m+1)
  ```
  In both cases, the inductive family has one parameter and one index.
  Recall that the actual number of parameters can be retrieved using the command `#print`.

* Remove support for `{}` annotation in the `structure` command.

* Several improvements to LSP server. Examples: "jump to definition" in mutually recursive sections, fixed incorrect hover information in "match"-expression patterns, "jump to definition" for pattern variables, fixed auto-completion in function headers, etc.

* In `macro ... xs:p* ...` and similar macro bindings of combinators, `xs` now has the correct type `Array Syntax`

* Identifiers in syntax patterns now ignore macro scopes during matching.

* Improve binder names for constructor auto implicit parameters. Example, given the inductive datatype
  ```lean
  inductive Member : α → List α → Type u
    | head : Member a (a::as)
    | tail : Member a bs → Member a (b::bs)
  ```
  before:
  ```lean
  #check @Member.head
  -- @Member.head : {x : Type u_1} → {a : x} → {as : List x} → Member a (a :: as)
  ```
  now:
  ```lean
  #check @Member.head
  -- @Member.head : {α : Type u_1} → {a : α} → {as : List α} → Member a (a :: as)
  ```

* Improve error message when constructor parameter universe level is too big.

* Add support for `for h : i in [start:stop] do .. ` where `h : i ∈ [start:stop]`. This feature is useful for proving
  termination of functions such as:
  ```lean
  inductive Expr where
    | app (f : String) (args : Array Expr)

  def Expr.size (e : Expr) : Nat := Id.run do
    match e with
    | app f args =>
      let mut sz := 1
      for h : i in [: args.size] do
        -- h.upper : i < args.size
        sz := sz + size (args.get ⟨i, h.upper⟩)
      return sz
  ```

* Add tactic `case'`. It is similar to `case`, but does not admit the goal on failure.
  For example, the new tactic is useful when writing tactic scripts where we need to use `case'`
  at `first | ... | ...`, and we want to take the next alternative when `case'` fails.

* Add tactic macro
  ```lean
  macro "stop" s:tacticSeq : tactic => `(repeat sorry)
  ```
  See discussion on [Zulip](https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Partial.20evaluation.20of.20a.20file).

* When displaying goals, we do not display inaccessible proposition names
if they do not have forward dependencies. We still display their types.
For example, the goal
  ```lean
  case node.inl.node
  β : Type u_1
  b : BinTree β
  k : Nat
  v : β
  left : Tree β
  key : Nat
  value : β
  right : Tree β
  ihl : BST left → Tree.find? (Tree.insert left k v) k = some v
  ihr : BST right → Tree.find? (Tree.insert right k v) k = some v
  h✝ : k < key
  a✝³ : BST left
  a✝² : ForallTree (fun k v => k < key) left
  a✝¹ : BST right
  a✝ : ForallTree (fun k v => key < k) right
  ⊢ BST left
  ```
  is now displayed as
  ```lean
  case node.inl.node
  β : Type u_1
  b : BinTree β
  k : Nat
  v : β
  left : Tree β
  key : Nat
  value : β
  right : Tree β
  ihl : BST left → Tree.find? (Tree.insert left k v) k = some v
  ihr : BST right → Tree.find? (Tree.insert right k v) k = some v
   : k < key
   : BST left
   : ForallTree (fun k v => k < key) left
   : BST right
   : ForallTree (fun k v => key < k) right
  ⊢ BST left
  ```

* The hypothesis name is now optional in the `by_cases` tactic.

* [Fix inconsistency between `syntax` and kind names](https://github.com/leanprover/lean4/issues/1090).
  The node kinds `numLit`, `charLit`, `nameLit`, `strLit`, and `scientificLit` are now called
  `num`, `char`, `name`, `str`, and `scientific` respectively. Example: we now write
  ```lean
  macro_rules | `($n:num) => `("hello")
  ```
  instead of
  ```lean
  macro_rules | `($n:numLit) => `("hello")
  ```

* (Experimental) New `checkpoint <tactic-seq>` tactic for big interactive proofs.

* Rename tactic `nativeDecide` => `native_decide`.

* Antiquotations are now accepted in any syntax. The `incQuotDepth` `syntax` parser is therefore obsolete and has been removed.

* Renamed tactic `nativeDecide` => `native_decide`.

* "Cleanup" local context before elaborating a `match` alternative right-hand-side. Examples:
  ```lean
  example (x : Nat) : Nat :=
    match g x with
    | (a, b) => _ -- Local context does not contain the auxiliary `_discr := g x` anymore

  example (x : Nat × Nat) (h : x.1 > 0) : f x > 0 := by
    match x with
    | (a, b) => _ -- Local context does not contain the `h✝ : x.fst > 0` anymore
  ```

* Improve `let`-pattern (and `have`-pattern) macro expansion. In the following example,
  ```lean
  example (x : Nat × Nat) : f x > 0 := by
    let (a, b) := x
    done
  ```
  The resulting goal is now `... |- f (a, b) > 0` instead of `... |- f x > 0`.

* Add cross-compiled [aarch64 Linux](https://github.com/leanprover/lean4/pull/1066) and [aarch64 macOS](https://github.com/leanprover/lean4/pull/1076) releases.

* [Add tutorial-like examples to our documentation](https://github.com/leanprover/lean4/tree/master/doc/examples), rendered using LeanInk+Alectryon.

````
