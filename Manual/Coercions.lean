/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoManual

import Manual.Meta
import Manual.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

open Lean (Syntax SourceInfo)


#doc (Manual) "Coercions" =>
%%%
tag := "coercions"
%%%

```lean (show := false)
section
open Lean (TSyntax Name)
variable {c1 c2 : Name} {α : Type u}
```


When the Lean elaborator is expecting one type but produces a term with a different type, it attempts to automatically insert a {deftech}_coercion_, which is a specially designated function from the term's type to the expected type.
Coercions make it possible to use specific types to represent data while interacting with APIs that expect less-informative types.
They also allow mathematical developments to follow the usual practice of “punning”, where the same symbol is used to stand for both an algebraic structure and its carrier set, with the precise meaning determined by context.


:::paragraph
Lean's standard library and metaprogramming APIs define many coercions.
Some examples include:

 * A {name}`Nat` may be used where an {name}`Int` is expected.
 * A {name}`Fin` may be used where a {name}`Nat` is expected.
 * An {lean}`α` may be used where an {lean}`Option α` is expected. The coercion wraps the value in {name}`some`.
 * An {lean}`α` may be used where a {lean}`Thunk α` is expected. The coercion wraps the term in a function to delay its evaluation.
 * When one syntax category {lean}`c1` embeds into another category {lean}`c2`, a coercion from {lean}`TSyntax c1` to {lean}`TSyntax c2` performs any necessary wrapping to construct a valid syntax tree.

Coercions are found using type class {tech}[synthesis].
The set of coercions can be extended by adding further instances of the appropriate type classes.
:::

```lean (show := false)
end
```

:::example "Coercions"

All of the following examples rely on coercions:

```lean
example (n : Nat) : Int := n
example (n : Fin k) : Nat := n
example (x : α) : Option α := x

def th (f : Int → String) (x : Nat) : Thunk String := f x

open Lean in
example (n : Ident) : Term := n
```

In the case of {name}`th`, using {keywordOf Lean.Parser.Command.print}`#print` demonstrates that evaluation of the function application is delayed until the thunk's value is requested:
```lean (name := thunkEval)
#print th
```
```leanOutput thunkEval
def th : (Int → String) → Nat → Thunk String :=
fun f x => { fn := fun x_1 => f ↑x }
```
:::


```lean (show := false)
section
variable {α : Type u}
```

Coercions are not used to resolve {tech}[generalized field notation]: only the inferred type of the term is considered.
However, a {tech}[type ascription] can be used to trigger a coercion to the type that has the desired generalized field.
Coercions are also not used to resolve {name}`OfNat` instances: even though there is a default instance for {lean}`OfNat Nat`, a coercion from {lean}`Nat` to {lean}`α` does not allow natural number literals to be used for {lean}`α`.

```lean (show := false)
end
```

```lean (show := false)
-- Test comment about field notation
/-- error: unknown constant 'Nat.bdiv' -/
#check_msgs in
#check Nat.bdiv

/-- info: Int.bdiv (x : Int) (m : Nat) : Int -/
#check_msgs in
#check Int.bdiv

/--
error: invalid field 'bdiv', the environment does not contain 'Nat.bdiv'
  n
has type
  Nat
-/
#check_msgs in
example (n : Nat) := n.bdiv 2

#check_msgs in
example (n : Nat) := (n : Int).bdiv 2
```

:::example "Coercions and Generalized Field Notation"

The name {lean (error := true)}`Nat.bdiv` is not defined, but {lean}`Int.bdiv` exists.
The coercion from {lean}`Nat` to {lean}`Int` is not considered when looking up the field `bdiv`:

```lean (error := true) (name := natBdiv)
example (n : Nat) := n.bdiv 2
```
```leanOutput natBdiv
invalid field 'bdiv', the environment does not contain 'Nat.bdiv'
  n
has type
  Nat
```

This is because coercions are only inserted when there is an expected type that differs from an inferred type, and generalized fields are resolved based on the inferred type of the term before the dot.
Coercions can be triggered by adding a type ascription, which additionally causes the inferred type of the entire ascription term to be {lean}`Int`, allowing the function {name}`Int.bdiv` to be found.
```lean
example (n : Nat) := (n : Int).bdiv 2
```
:::

::::example "Coercions and `OfNat`"
{lean}`Bin` is an inductive type that represents binary numbers.
```lean
inductive Bin where
  | done
  | zero : Bin → Bin
  | one : Bin → Bin

def Bin.toString : Bin → String
  | .done => ""
  | .one b => b.toString ++ "1"
  | .zero b => b.toString ++ "0"

instance : ToString Bin where
  toString
    | .done => "0"
    | b => Bin.toString b
```

Binary numbers can be converted to natural numbers by repeatedly applying {lean}`Bin.succ`:
```lean
def Bin.succ (b : Bin) : Bin :=
  match b with
  | .done => Bin.done.one
  | .zero b => .one b
  | .one b => .zero b.succ

def Bin.ofNat (n : Nat) : Bin :=
  match n with
  | 0 => .done
  | n + 1 => (Bin.ofNat n).succ
```

```lean (show := false)
--- Internal tests
/-- info: [0, 1, 10, 11, 100, 101, 110, 111, 1000] -/
#check_msgs in
#eval [
  Bin.done,
  Bin.done.succ,
  Bin.done.succ.succ,
  Bin.done.succ.succ.succ,
  Bin.done.succ.succ.succ.succ,
  Bin.done.succ.succ.succ.succ.succ,
  Bin.done.succ.succ.succ.succ.succ.succ,
  Bin.done.succ.succ.succ.succ.succ.succ.succ,
  Bin.done.succ.succ.succ.succ.succ.succ.succ.succ]

def Bin.toNat : Bin → Nat
  | .done => 0
  | .zero b => 2 * b.toNat
  | .one b => 2 * b.toNat + 1

def Bin.double : Bin → Bin
  | .done => .done
  | other => .zero other

theorem Bin.toNat_succ_eq_succ {b : Bin} : b.toNat = n → b.succ.toNat = n + 1 := by
  intro hEq
  induction b generalizing n <;> simp_all +arith [Bin.toNat, Bin.succ]

theorem Bin.toNat_double_eq_double {b : Bin} : b.toNat = n → b.double.toNat = n * 2 := by
  intro hEq
  induction b generalizing n <;> simp_all +arith [Bin.toNat, Bin.double]

theorem Bin.ofNat_toNat_eq {n : Nat} : (Bin.ofNat n).toNat = n := by
  induction n <;> simp_all [Bin.ofNat, Bin.toNat, Bin.toNat_succ_eq_succ]
```


Even if {lean}`Bin.ofNat` is registered as a coercion, natural number literals cannot be used for {lean}`Bin`:
```lean (name := nineFail) (error := true)
attribute [coe] Bin.ofNat

instance : Coe Nat Bin where
  coe := Bin.ofNat

#eval (9 : Bin)
```
```leanOutput nineFail
failed to synthesize
  OfNat Bin 9
numerals are polymorphic in Lean, but the numeral `9` cannot be used in a context where the expected type is
  Bin
due to the absence of the instance above

Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
This is because coercions are inserted in response to mismatched types, but a failure to synthesize an {name}`OfNat` instance is not a type mismatch.


The coercion can be used in the definition of the {lean}`OfNat Bin` instance:
```lean (name := ten)
instance : OfNat Bin n where
  ofNat := n

#eval (10 : Bin)
```
```leanOutput ten
1010
```
::::

Most new coercions can be defined by declaring an instance of the {name}`Coe` {tech}[type class] and applying the {attr}`coe` attribute to the function that performs the coercion.
To enable more control over coercions or to enable them in more contexts, Lean provides further classes that can be implemented, described in the rest of this chapter.

:::example "Defining Coercions: Decimal Numbers"
Decimal numbers can be defined as arrays of digits.

```lean
structure Decimal where
  digits : Array (Fin 10)
```

Adding a coercion allows them to be used in contexts that expect {lean}`Nat`, but also contexts that expect any type that {lean}`Nat` can be coerced to.

```lean
@[coe]
def Decimal.toNat (d : Decimal) : Nat :=
  d.digits.foldl (init := 0) fun n d => n * 10 + d.val

instance : Coe Decimal Nat where
  coe := Decimal.toNat
```

This can be demonstrated by treating a {lean}`Decimal` as an {lean}`Int` as well as a {lean}`Nat`:
```lean (name := digival)
def twoHundredThirteen : Decimal where
  digits := #[2, 1, 3]

def one : Decimal where
  digits := #[1]

#eval (one : Int) - (twoHundredThirteen : Nat)
```
```leanOutput digival
-212
```

:::

{docstring Coe}



# Coercion Insertion
%%%
tag := "coercion-insertion"
%%%

:::paragraph
The process of searching for a coercion from one type to another is called {deftech}_coercion insertion_.
Coercion insertion is attempted in the following situations where an error would otherwise occur:

 * The expected type for a term is not equal to the type found for the term.

 * A type or proposition is expected, but the term's type is not a {tech}[universe].

 * A term is applied as though it were a function, but its type is not a function type.

Coercions are also inserted when they are explicitly requested.
Each situation in which coercions may be inserted has a corresponding prefix operator that triggers the appropriate insertion.
:::

```lean (show := false)
section
variable {α : Type u} {α' : Type u'} {β : Type u} [Coe α α'] [Coe α' β] (e : α)
```

Because coercions are inserted automatically, nested {tech}[type ascriptions] provide a way to precisely control the types involved in a coercion.
If {lean}`α` and {lean}`β` are not the same type, {lean}`((e : α) : β)` arranges for {lean}`e` to have type {lean}`α` and then inserts a coercion from {lean}`α` to {lean}`β`.

```lean (show := false)
end
```

When a coercion is discovered, the instances used to find it are unfolded and removed from the resulting term.
To the extent possible, calls to {name}`Coe.coe` and related functions do not occur in the final term.
This process of unfolding makes terms more readable.
Even more importantly, it means that coercions can control the evaluation of the coerced terms by wrapping them in functions.

:::example "Controlling Evaluation with Coercions"

The structure {name}`Later` represents a term that can be evaluated in the future, by calling the contained function.

```lean
structure Later (α : Type u) where
  get : Unit → α
```

A coercion from any value to a later value is performed by creating a function that wraps it.
```lean
instance : CoeTail α (Later α) where
  coe x := { get := fun () => x }
```

However, if coercion insertion resulted in an application of {name}`CoeTail.coe`, then this coercion would not have the desired effect at runtime, because the coerced value would be evaluated and then saved in the function's closure.
Because coercion implementations are unfolded, this instance is nonetheless useful.

```lean
def tomorrow : Later String :=
  (Nat.fold 10000
    (init := "")
    (fun _ _ s => s ++ "tomorrow") : String)
```
Printing the resulting definition shows that the computation is inside the function's body:
```lean (name := tomorrow)
#print tomorrow
```
```leanOutput tomorrow
def tomorrow : Later String :=
{ get := fun x => Nat.fold 10000 (fun x x s => s ++ "tomorrow") "" }
```
:::

```lean (show := false)
section
variable {α : Type u}
```
:::example "Duplicate Evaluation in Coercions"
Because the contents of {lean}`Coe` instances are unfolded during coercion insertion, coercions that use their argument more than once should be careful to ensure that evaluation occurs just once.
This can be done by using a helper function that is not part of the instance, or by using {keywordOf Lean.Parser.Term.let}`let` to evaluate the coerced term and then re-use its resulting value.

The structure {name}`Twice` requires that both fields have the same value:
```lean
structure Twice (α : Type u) where
  first : α
  second : α
  first_eq_second : first = second
```

One way to define a coercion from {lean}`α` to {lean}`Twice α` is with a helper function {name}`twice`.
The {attr}`coe` attribute marks it as a coercion so it can be shown correctly in proof goals and error messages.
```lean
@[coe]
def twice (x : α) : Twice α where
  first := x
  second := x
  first_eq_second := rfl

instance : Coe α (Twice α) := ⟨twice⟩
```
When the {name}`Coe` instance is unfolded, the call to {name}`twice` remains, which causes its argument to be evaluated before the body of the function is executed.
As a result, the {keywordOf Lean.Parser.Term.dbgTrace}`dbg_trace` executes just once:
```lean (name := eval1)
#eval ((dbg_trace "hello"; 5 : Nat) : Twice Nat)
```
```leanOutput eval1
hello
```
```leanOutput eval1
{ first := 5, second := 5, first_eq_second := _ }
```

Inlining the helper into the {name}`Coe` instance results in a term that duplicates the {keywordOf Lean.Parser.Term.dbgTrace}`dbg_trace`:
```lean (name := eval2)
instance : Coe α (Twice α) where
  coe x := ⟨x, x, rfl⟩

#eval ((dbg_trace "hello"; 5 : Nat) : Twice Nat)
```
```leanOutput eval2
hello
hello
```
```leanOutput eval2
{ first := 5, second := 5, first_eq_second := _ }
```

Introducing an intermediate name for the result of the evaluation prevents the duplicated work:
```lean (name := eval3)
instance : Coe α (Twice α) where
  coe x := let y := x; ⟨y, y, rfl⟩

#eval ((dbg_trace "hello"; 5 : Nat) : Twice Nat)
```
```leanOutput eval3
hello
```
```leanOutput eval3
{ first := 5, second := 5, first_eq_second := _ }
```

:::
```lean (show := false)
end
```


# Coercing Between Types
%%%
tag := "ordinary-coercion"
%%%

:::paragraph
Coercions between types are inserted when the Lean elaborator successfully constructs a term, inferring its type, in a context where a term of some other type was expected.
Before signaling an error, the elaborator attempts to insert a coercion from the inferred type to the expected type by synthesizing an instance of {lean}`CoeT`.
There are two ways that this might succeed:
 1. There could be a chain of coercions from the inferred type to the expected type through a number of intermediate types.
    These chained coercions are selected based on the inferred type and the expected type, but not the term being coerced.
 2. There could be a single dependent coercion from the inferred type to the expected type.
    Dependent coercions take the term being coerced into account as well as the inferred and expected types, but they cannot be chained.
:::

The simplest way to define a non-dependent coercion is by implementing a {name}`Coe` instance, which is enough to synthesize a {name}`CoeT` instance.
This instance participates in chaining, and may be applied any number of times.
The expected type of the expression is used to drive synthesis of {name}`Coe` instances, rather than the inferred type.
For instances that can be used at most once, or instances in which the inferred type should drive synthesis, one of the other coercion classes may be needed.

:::example "Defining Coercions"
The type {lean}`Even` represents the even natural numbers.

```lean
structure Even where
  number : Nat
  isEven : number % 2 = 0
```

A coercion allows even numbers to be used where natural numbers are expected.
The {attr}`coe` attribute marks the projection as a coercion so that it can be shown accordingly in proof states and error messages, as described in the {ref "coercion-impl"}[section on implementing coercions].
```lean
attribute [coe] Even.number

instance : Coe Even Nat where
  coe := Even.number
```
With this coercion in place, even numbers can be used where natural numbers are expected.
```lean (name := four)
def four : Even := ⟨4, by omega⟩

#eval (four : Nat) + 1
```
```leanOutput four
5
```

Due to coercion chaining, there is also a coercion from {name}`Even` to {name}`Int` formed by chaining the {inst}`Coe Even Nat` instance with the existing coercion from {name}`Nat` to {name}`Int`:
```lean name := four'
#eval (four : Int) - 5
```
```leanOutput four'
-1
```
:::

{deftech}[Dependent coercions] are needed when the specific term being coerced is required in order to determine whether or how to coerce the term: for example, only decidable propositions can be coerced to {name}`Bool`, so the proposition in question must occur as part of the instance's type so that it can require the {name}`Decidable` instance.
Non-dependent coercions are used whenever all values of the inferred type can be coerced to the target type.

:::example "Defining Dependent Coercions"
The string "four" can be coerced into the natural number {lean type:="Nat"}`4` with this instance declaration:
````lean (name := fourCoe)
instance : CoeDep String "four" Nat where
  coe := 4

#eval ("four" : Nat)
````
```leanOutput fourCoe
4
```

Ordinary type errors are produced for other strings:
```lean (error := true) (name := threeCoe)
#eval ("three" : Nat)
```
```leanOutput threeCoe
type mismatch
  "three"
has type
  String : Type
but is expected to have type
  Nat : Type
```

:::


```lean (show := false)
section
variable {α α' α'' β β' «…» γ: Sort _}

macro "…":term => Lean.mkIdentFromRef `«…»

variable [CoeHead α α'] [CoeOut α' …] [CoeOut … α''] [Coe α'' …] [Coe … β'] [CoeTail β' γ]


```

:::paragraph
Non-dependent coercions may be chained: if there is a coercion from {lean}`α` to {lean}`β` and from {lean}`β` to {lean}`γ`, then there is also a coercion from {lean}`α` to {lean}`γ`.
{index subterm:="of coercions"}[chain]
The chain should be in the form {name}`CoeHead`$`?`{name}`CoeOut`$`*`{name}`Coe`$`*`{name}`CoeTail`$`?`, which is to say it may consist of:

 * An optional instance of {inst}`CoeHead α α'`, followed by
 * Zero or more instances of {inst}`CoeOut α' …`, …, {inst}`CoeOut … α''`, followed by
 * Zero or more instances of {inst}`Coe α'' …`, …, {inst}`Coe … β'`, followed by
 * An optional instance of {inst}`CoeTail β' γ`

Most coercions can be implemented as instances of {name}`Coe`.
{name}`CoeHead`, {name}`CoeOut`, and {name}`CoeTail` are needed in certain special situations.

:::



{name}`CoeHead` and {name}`CoeOut` instances are chained from the inferred type towards the expected type.
In other words, information in the type found for the term is used to resolve a chain of instances.
{name}`Coe` and {name}`CoeTail` instances are chained from the expected type towards the inferred type, so information in the expected type is used to resolve a chain of instances.
If these chains meet in the middle, a coercion has been found.
This is reflected in their type signatures: {name}`CoeHead` and {name}`CoeOut` use {tech}[semi-output parameters] for the coercion's target, while {name}`Coe` and {name}`CoeTail` use {tech}[semi-output parameters] for the coercions' source.

When an instance provides a value for a {tech}[semi-output parameter], the value is used during instance synthesis.
However, if no value is provided, then a value may be assigned by the synthesis algorithm.
Consequently, every semi-output parameter should be assigned a type when an instance is selected.
This means that {name}`CoeOut` should be used when the variables that occur in the coercion's output are a subset of those in its input, and {name}`Coe` should be used when the variables in the input are a subset of those in the output.

:::example "`CoeOut` vs `Coe` instances"
A {name}`Truthy` value is a value paired with an indication of whether it should be considered to be true or false.
A {name}`Decision` is either {name Decision.yes}`yes`, {name Decision.no}`no`, or {name Decision.maybe}`maybe`, with the latter containing further data for consideration.

```lean
structure Truthy (α : Type) where
  val : α
  isTrue : Bool

inductive Decision (α : Type) where
  | yes
  | maybe (val : α)
  | no
```

{noVale "Made-up word for example purposes"}[“Truthy”] values can be converted to {name}`Bool`s by forgetting the contained value.
{name}`Bool`s can be converted to {name}`Decision`s by discounting the {name Decision.maybe}`maybe` case.
```lean
@[coe]
def Truthy.toBool : Truthy α → Bool :=
  Truthy.isTrue

@[coe]
def Decision.ofBool : Bool → Decision α
  | true => .yes
  | false => .no
```

{name}`Truthy.toBool` must be a {name}`CoeOut` instance, because the target of the coercion contains fewer unknown type variables than the source, while {name}`Decision.ofBool` must be a {name}`Coe` instance, because the source of the coercion contains fewer variables than the target:
```lean
instance : CoeOut (Truthy α) Bool := ⟨Truthy.isTrue⟩

instance : Coe Bool (Decision α) := ⟨Decision.ofBool⟩
```

With these instances, coercion chaining works:
```lean name := chainTruthiness
#eval ({ val := 1, isTrue := true : Truthy Nat } : Decision String)
```
```leanOutput chainTruthiness
Decision.yes
```

Attempting to use the wrong class leads to an error:
```lean name:=coeOutErr error:=true
instance : Coe (Truthy α) Bool := ⟨Truthy.isTrue⟩
```
```leanOutput coeOutErr
instance does not provide concrete values for (semi-)out-params
  Coe (Truthy ?α) Bool
```

:::


```lean (show := false)
end
```

{docstring CoeHead}

{docstring CoeOut}

{docstring CoeTail}

Instances of {name}`CoeT` can be synthesized when an appropriate chain of instances exists, or when there is a single applicable {name}`CoeDep` instance.{margin}[When coercing from {lean}`Nat` to another type, a {name}`NatCast` instances also suffices.]
If both exist, then the {name}`CoeDep` instance takes priority.

{docstring CoeT}

```lean (show := false)
section
variable {α β : Sort _} {e : α} [CoeDep α e β]
```

Dependent coercions may not be chained.
As an alternative to a chain of coercions, a term {lean}`e` of type {lean}`α` can be coerced to {lean}`β` using an instance of {inst}`CoeDep α e β`.
Dependent coercions are useful in situations where only some of the values can be coerced; this mechanism is used to coerce only decidable propositions to {lean}`Bool`.
They are also useful when the value itself occurs in the coercion's target type.

```lean (show := false)
end
```

{docstring CoeDep}

:::example "Dependent Coercion"
```lean (show := false)
universe u
```

A type of non-empty lists can be defined as a pair of a list and a proof that it is not empty.
This type can be coerced to ordinary lists by applying the projection:

```lean
structure NonEmptyList (α : Type u) : Type u where
  contents : List α
  non_empty : contents ≠ []

instance : Coe (NonEmptyList α) (List α) where
  coe xs := xs.contents
```

The coercion works as expected:
```lean
def oneTwoThree : NonEmptyList Nat := ⟨[1, 2, 3], by simp⟩

#eval (oneTwoThree : List Nat) ++ [4]
```

Arbitrary lists cannot, however, be coerced to non-empty lists, because some arbitrarily-chosen lists may indeed be empty:

```lean (error := true) (name := coeFail) (keep := false)
instance : Coe (List α) (NonEmptyList α) where
  coe xs := ⟨xs, _⟩
```
```leanOutput coeFail
don't know how to synthesize placeholder for argument 'non_empty'
context:
α : Type u_1
xs : List α
⊢ xs ≠ []
```

A dependent coercion can restrict the domain of the coercion to only lists that are not empty:
```lean (name := coeOk)
instance : CoeDep (List α) (x :: xs) (NonEmptyList α) where
  coe := ⟨x :: xs, by simp⟩

#eval ([1, 2, 3] : NonEmptyList Nat)
```
```leanOutput coeOk
{ contents := [1, 2, 3], non_empty := _ }
```


Dependent coercion insertion requires that the term to be coerced syntactically matches the term in the instance header.
Lists that are known to be non-empty, but which are not syntactically instances of {lean type:= "{α : Type u} → α → List α → List α"}`(· :: ·)`, cannot be coerced with this instance.
```lean (error := true) (name := coeFailDep)
#check
  fun (xs : List Nat) =>
    let ys : List Nat := xs ++ [4]
    (ys : NonEmptyList Nat)
```
When coercion insertion fails, the original type error is reported:
```leanOutput coeFailDep
type mismatch
  ys
has type
  List Nat : Type
but is expected to have type
  NonEmptyList Nat : Type
```

:::

:::syntax term (title := "Coercions")
```grammar
↑$_:term
```

Coercions can be explicitly placed using the prefix operator {keywordOf coeNotation}`↑`.
:::

Unlike using nested {tech}[type ascriptions], the {keywordOf coeNotation}`↑` syntax for placing coercions does not require the involved types to be written explicitly.

:::example "Controlling Coercion Insertion"

Instance synthesis and coercion insertion interact with one another.
Synthesizing an instance may make type information known that later triggers coercion insertion.
The specific placement of coercions may matter.

In this definition of {lean}`sub`, the {inst}`Sub Int` instance is synthesized based on the function's return type.
This instance requires that the two parameters also be {lean}`Int`s, but they are {lean}`Nat`s.
Coercions are inserted around each argument to the subtraction operator.
This can be seen in the output of {keywordOf Lean.Parser.Command.print}`#print`.

```lean (name := subThenCoe)
def sub (n k : Nat) : Int := n - k

#print sub
```
```leanOutput subThenCoe
def sub : Nat → Nat → Int :=
fun n k => ↑n - ↑k
```

Placing the coercion operator outside the subtraction causes the elaborator to attempt to infer a type for the subtraction and then insert a coercion.
Because the arguments are both {lean}`Nat`s, the {inst}`Sub Nat` instance is selected, leading to the difference being a {lean}`Nat`.
The difference is then coerced to an {lean}`Int`.
```lean (name:=coeThenSub)
def sub' (n k : Nat) : Int := ↑ (n - k)

#print sub'
```

These two functions are not equivalent because subtraction of natural numbers truncates at zero:
```lean (name := subRes)
#eval sub 4 8
```
```leanOutput subRes
-4
```
```lean (name := subMark)
#eval sub' 4 8
```
```leanOutput subMark
0
```

:::


## Implementing Coercions
%%%
tag := "coercion-impl"
%%%

The appropriate {name}`CoeHead`, {name}`CoeOut`, {name}`Coe`, or {name}`CoeTail` instance is sufficient to cause a desired coercion to be inserted.
However, the implementation of the coercion should be registered as a coercion using the {attr}`coe` attribute.
This causes Lean to display uses of the coercion with the {keywordOf coeNotation}`↑` operator.
It also causes the {tactic}`norm_cast` tactic to treat the coercion as a cast, rather than as an ordinary function.

:::syntax attr (title := "Coercion Declarations")
```grammar
coe
```

{includeDocstring Lean.Attr.coe}

:::

:::example "Implementing Coercions"
The {tech}[enum inductive] type {lean}`Weekday` represents the days of the week:
```lean
inductive Weekday where
  | mo | tu | we | th | fr | sa | su
```

As a seven-element type, it contains the same information as {lean}`Fin 7`.
There is a bijection:
```lean
def Weekday.toFin : Weekday → Fin 7
  | mo => 0
  | tu => 1
  | we => 2
  | th => 3
  | fr => 4
  | sa => 5
  | su => 6

def Weekday.fromFin : Fin 7 → Weekday
  | 0 => mo
  | 1 => tu
  | 2 => we
  | 3 => th
  | 4 => fr
  | 5 => sa
  | 6 => su
```

```lean (show := false)
theorem Weekday.toFin_fromFin_id : Weekday.toFin (Weekday.fromFin n) = n := by
  repeat (cases ‹Fin (_ + 1)› using Fin.cases; case zero => rfl)
  apply Fin.elim0; assumption

theorem Weekday.fromFin_toFin_id : Weekday.fromFin (Weekday.toFin w) = w := by
  cases w <;> rfl
```

Each type can be coerced to the other:
```lean
instance : Coe Weekday (Fin 7) where
  coe := Weekday.toFin

instance : Coe (Fin 7) Weekday where
  coe := Weekday.fromFin
```

While this works, instances of the coercions that occur in Lean's output are not presented using the coercion operator, which is what Lean users expect.
Instead, the name {lean}`Weekday.fromFin` is used explicitly:
```lean (name := wednesday)
def wednesday : Weekday := (2 : Fin 7)

#print wednesday
```
```leanOutput wednesday
def wednesday : Weekday :=
Weekday.fromFin 2
```


Adding the {attr}`coe` attribute to the definition of a coercion causes it to be displayed using the coercion operator:
```lean (name := friday)
attribute [coe] Weekday.fromFin
attribute [coe] Weekday.toFin

def friday : Weekday := (5 : Fin 7)

#print friday
```
```leanOutput friday
def friday : Weekday :=
↑5
```

:::

## Coercions from Natural Numbers and Integers
%%%
tag := "nat-api-cast"
%%%

The type classes {name}`NatCast` and {name}`IntCast` are special cases of {name}`Coe` that are used to define a coercion from {lean}`Nat` or {lean}`Int` to some other type that is in some sense canonical.
They exist to enable better integration with large libraries of mathematics, such as [Mathlib](https://github.com/leanprover-community/mathlib4), that make heavy use of coercions to map from the natural numbers or integers to other structures (typically rings).
Ideally, the coercion of a natural number or integer into these structures is a {tech}[simp normal form], because it is a convenient way to denote them.

When the coercion application is expected to be the {tech}[simp normal form] for a type, it is important that _all_ such coercions are {tech key:="definitional equality"}[definitionally equal] in practice.
Otherwise, the {tech}[simp normal form] would need to choose a single chained coercion path, but lemmas could accidentally stated using a different path.
Because {tactic}`simp`'s internal index is based on the underlying structure of the term, rather than its presentation in the surface syntax, these differences would cause the lemmas to not be applied where expected.
{lean}`NatCast` and {lean}`IntCast` instances, on the other hand, should be defined such that they are always {tech key:="definitional equality"}[definitionally equal], avoiding the problem.
The Lean standard library's instances are arranged such that {name}`NatCast` or {name}`IntCast` instances are chosen preferentially over chains of coercion instances during coercion insertion.
They can also be used as {name}`CoeOut` instances, allowing a graceful fallback to coercion chaining when needed.

{docstring NatCast}

{docstring Nat.cast}

{docstring IntCast}

{docstring Int.cast}


# Coercing to Sorts
%%%
tag := "sort-coercion"
%%%

The Lean elaborator expects types in certain positions without necessarily being able to determine the type's {tech}[universe] ahead of time.
For example, the term following the colon in a definition header might be a proposition or a type.
The ordinary coercion mechanism is not applicable because it requires a specific expected type, and there's no way to express that the expected type could be _any_ universe in the {name}`Coe` class.

When a term is elaborated in a position where a proposition or type is expected, but the inferred type of the elaborated term is not a proposition or type, Lean  attempts to recover from the error by synthesizing an instance of {name}`CoeSort`.
If the instance is found, and the resulting type is itself a type, then it the coercion is inserted and unfolded.

Not every situation in which the elaborator expects a universe requires {name}`CoeSort`.
In some cases, a particular universe is available as an expected type.
In these situations, ordinary coercion insertion using {name}`CoeT` is used.
Instances of {lean}`CoeSort` can be used to synthesize instances of {lean}`CoeOut`, so no separate instance is needed to support this use case.
In general, coercions to types should be implemented as {name}`CoeSort`.

{docstring CoeSort}


:::syntax term (title := "Explicit Coercion to Sorts")
```grammar
↥ $_:term
```

Coercions to sorts can be explicitly triggered using the {keyword}`↥` prefix operator.
:::

::: example "Sort Coercions"

A monoid is a type equipped with an associative binary operation and an identity element.
While monoid structure can be defined as a type class, it can also be defined as a structure that “bundles up” the structure with the type:
```lean
structure Monoid where
  Carrier : Type u
  op : Carrier → Carrier → Carrier
  id : Carrier
  op_assoc :
    ∀ (x y z : Carrier), op x (op y z) = op (op x y) z
  id_op_identity : ∀ (x : Carrier), op id x = x
  op_id_identity : ∀ (x : Carrier), op x id = x
```

The type {lean type := "Type 1"}`Monoid` does not indicate the carrier:
```lean
def StringMonoid : Monoid where
  Carrier := String
  op := (· ++ ·)
  id := ""
  op_assoc := by intros; simp [String.append_assoc]
  id_op_identity := by intros; simp
  op_id_identity := by intros; simp
```

However, a {name}`CoeSort` instance can be implemented that applies the {name}`Monoid.Carrier` projection when a monoid is used in a position where Lean would expect a type:
```lean
instance : CoeSort Monoid (Type u) where
  coe m := m.Carrier

example : StringMonoid := "hello"
```
:::

:::example "Sort Coercions as Ordinary Coercions"
The {tech}[inductive type] {name}`NatOrBool` represents the types {name}`Nat` and {name}`Bool`.
The can be coerced to the actual types {name}`Nat` and {name}`Bool`:
```lean
inductive NatOrBool where
  | nat | bool

@[coe]
abbrev NatOrBool.asType : NatOrBool → Type
  | .nat => Nat
  | .bool => Bool

instance : CoeSort NatOrBool Type where
  coe := NatOrBool.asType

open NatOrBool
```

The {name}`CoeSort` instance is used when {lean}`nat` occurs to the right of a colon:
```lean
def x : nat := 5
```

When an expected type is available, ordinary coercion insertion is used.
In this case, the {name}`CoeSort` instance is used to synthesize a {lean}`CoeOut NatOrBool Type` instance, which chains with the {inst}`Coe Type (Option Type)` instance to recover from the type error.
```lean
def y : Option Type := bool
```
:::

# Coercing to Function Types
%%%
tag := "fun-coercion"
%%%

Another situation where an expected type is not generally available is the function position in a function application term.
Dependent function types are common; together with {tech}[implicit] parameters, they cause information to flow from the elaboration of one argument to the elaboration of the others.
Attempting to deduce the type required for the function from the expected type of the entire application term and individually-inferred types of arguments will often fail.
In these situations, Lean uses the {name}`CoeFun` type class to coerce a non-function in an application position into a function.
Like {name}`CoeSort`, {name}`CoeFun` instances do not chain with other coercions while inserting a function coercion, but they can be used as {name}`CoeOut` instances during ordinary coercion insertion.

The second parameter to {name}`CoeFun` is an output parameter that determines the resulting function type.
This output parameter is function that computes the function type from the term that's being coerced, rather than the function type itself.
Unlike {name}`CoeDep`, the term itself is not taken into account during instance synthesis; it can, however, be used to create dependently typed coercions where the function type is determined by the term.


{docstring CoeFun}

:::syntax term (title := "Explicit Coercion to Functions")
```grammar
⇑ $_:term
```
:::

```lean (show := false)
section
variable {α : Type u} {β : Type v}
```
:::example "Coercing Decorated Functions to Function Types"
The structure {lean}`NamedFun α β` pairs a function from {lean}`α` to {lean}`β` with a name.

```lean
structure NamedFun (α : Type u) (β : Type v) where
  function : α → β
  name : String
```

Existing functions can be named:
```lean
def succ : NamedFun Nat Nat where
  function n := n + 1
  name := "succ"

def asString [ToString α] : NamedFun α String where
  function := ToString.toString
  name := "asString"

def append : NamedFun (List α) (List α → List α) where
  function := (· ++ ·)
  name := "append"
```

Named functions can also be composed:
```lean
def NamedFun.comp
    (f : NamedFun β γ)
    (g : NamedFun α β) :
    NamedFun α γ where
  function := f.function ∘ g.function
  name := f.name ++ " ∘ " ++ g.name
```


Unlike ordinary functions, named functions have a reasonable representation as a string:
```lean
instance : ToString (NamedFun α α'') where
  toString f := s!"#<{f.name}>"
```
```lean (name := compDemo)
#eval asString.comp succ
```
```leanOutput compDemo
#<asString ∘ succ>
```

A {name}`CoeFun` instance allows them to be applied just like ordinary functions:
```lean
instance : CoeFun (NamedFun α α'') (fun _ => α → α'') where
  coe | ⟨f, _⟩ => f
```
```lean (name := appendDemo)
#eval append [1, 2, 3] [4, 5, 6]
```
```leanOutput appendDemo
[1, 2, 3, 4, 5, 6]
```
:::
```lean (show := false)
end
```

:::example "Dependent Coercion to Functions"
Sometimes, the type of the resulting function depends on the specific value that is being coerced.
A {lean}`Writer` represents a means of appending a representation of some value to a string:
```lean
structure Writer where
  Writes : Type u
  write : Writes → String → String

def natWriter : Writer where
  Writes := Nat
  write n out := out ++ toString n

def stringWriter : Writer where
  Writes := String
  write s out := out ++ s
```

Because the type of the parameter expected by the inner function depend on the {lean}`Writer.Writes` field, the {name}`CoeFun` instance extracts the field:
```lean
instance :
    CoeFun Writer (·.Writes → String → String) where
  coe w := w.write
```

With this instance, concrete {name}`Writer`s can be used as functions:
```lean (name := writeTwice)
#eval "" |> natWriter (5 : Nat) |> stringWriter " hello"
```
```leanOutput writeTwice
"5 hello"
```
:::

:::example "Coercing to Function Types"

A well-typed interpreter is an interpreter for a programming language that uses indexed families to rule out run-time type errors.
Functions written in the interpreted language can be interpreted as Lean functions, but their underlying source code can also be inspected.

The first step in the well-typed interpreter is to select the subset of Lean types that can be used.
These types are represented by an {tech}[inductive type] of codes {name}`Ty` and a function that maps these codes to actual types.
```lean
inductive Ty where
  | nat
  | arr (dom cod : Ty)

abbrev Ty.interp : Ty → Type
  | .nat => Nat
  | .arr t t' => t.interp → t'.interp
```

The language itself is represented by an {tech}[indexed family] over variable contexts and result types.
Variables are represented by [de Bruijn indices](https://en.wikipedia.org/wiki/De_Bruijn_index).
```lean
inductive Tm : List Ty → Ty → Type where
  | zero : Tm Γ .nat
  | succ (n : Tm Γ .nat) : Tm Γ .nat
  | rep (n : Tm Γ .nat)
    (start : Tm Γ t)
    (f : Tm Γ (.arr .nat (.arr t t))) :
    Tm Γ t
  | lam (body : Tm (t :: Γ) t') : Tm Γ (.arr t t')
  | app (f : Tm Γ (.arr t t')) (arg : Tm Γ t) : Tm Γ t'
  | var (i : Fin Γ.length) : Tm Γ Γ[i]
deriving Repr
```


Because the {name}`OfNat` instance for {name}`Fin` requires that the upper bound be non-zero, {name}`Tm.var` can be inconvenient to use with numeric literals.
The helper {name}`Tm.v` can be used to avoid the need for type annotations in these cases.
```lean
def Tm.v
    (i : Fin (Γ.length + 1)) :
    Tm (t :: Γ) (t :: Γ)[i] :=
  .var (Γ := t :: Γ) i
```

A function that adds two natural numbers uses the {name Tm.rep}`rep` operation to apply the successor {name}`Tm.succ` repeatedly.
```lean
def plus : Tm [] (.arr .nat (.arr .nat .nat)) :=
  .lam <| .lam <| .rep (.v 1) (.v 0) (.lam (.lam (.succ (.v 0))))
```


Each typing context can be interpreted as a type of run-time environments that provide a value for each variable in the context:
```lean
def Env : List Ty → Type
  | [] => Unit
  | t :: Γ => t.interp × Env Γ

def Env.empty : Env [] := ()

def Env.extend (ρ : Env Γ) (v : t.interp) : Env (t :: Γ) :=
  (v, ρ)

def Env.get (i : Fin Γ.length) (ρ : Env Γ) : Γ[i].interp :=
  match Γ, ρ, i with
  | _::_, (v, _), ⟨0, _⟩ => v
  | _::_, (_, ρ'), ⟨i+1, _⟩ => ρ'.get ⟨i, by simp_all⟩
```

Finally, the interpreter is a recursive function over the term:
```lean
def Tm.interp (ρ : Env α'') : Tm α'' t → t.interp
  | .zero => 0
  | .succ n => n.interp ρ + 1
  | .rep n start f =>
    let f' := f.interp ρ
    (n.interp ρ).fold (fun n _ x => f' n x) (start.interp ρ)
  | .lam body => fun x => body.interp (ρ.extend x)
  | .app f arg => f.interp ρ (arg.interp ρ)
  | .var i => ρ.get i
```

Coercing a {name}`Tm` to a function consists of calling the interpreter.

```lean
instance : CoeFun (Tm [] α'') (fun _ => α''.interp) where
  coe f := f.interp .empty
```

Because functions are represented by a first-order inductive type, their code can be inspected:
```lean (name := evalPlus)
#eval plus
```
```leanOutput evalPlus
Tm.lam (Tm.lam (Tm.rep (Tm.var 1) (Tm.var 0) (Tm.lam (Tm.lam (Tm.succ (Tm.var 0))))))
```

At the same time, due to the coercion, they can be applied just like native Lean functions:
```lean (name := eight)
#eval plus 3 5
```
```leanOutput eight
8
```

:::



# Implementation Details
%%%
tag := "coercion-impl-details"
%%%


Only ordinary coercion insertion uses chaining.
Inserting coercions to a {ref "sort-coercion"}[sort] or a {ref "fun-coercion"}[function] uses ordinary instance synthesis.
Similarly, {tech}[dependent coercions] are not chained.

## Unfolding Coercions
%%%
tag := "coercion-unfold-impl"
%%%

The coercion insertion mechanism unfolds applications of coercions, which allows them to control the specific shape of the resulting term.
This is important both to ensure readable proof goals and to control evaluation of the coerced term in compiled code.
Unfolding coercions is controlled by the {attr}`coe_decl` attribute, which is applied to each coercion method (e.g. {name}`Coe.coe`).
This attribute should be considered part of the internals of the coercion mechanism, rather than part of the public coercion API.


## Coercion Chaining
%%%
tag := "coercion-chain-impl"
%%%

:::paragraph

Coercion chaining is implemented through a collection of auxiliary type classes.
Users should not write instances of these classes directly, but knowledge of their structure can be useful when diagnosing the reason why a coercion was not inserted as expected.
The specific rules governing the ordering of instances in the chain (namely, that it should match {name}`CoeHead`﻿`?`{name}`CoeOut`﻿`*`{name}`Coe`﻿`*`{name}`CoeTail`﻿`?`) are implemented by the following type classes:

 * {name}`CoeTC` is the transitive closure of {name}`Coe` instances.

 * {name}`CoeOTC` is the middle of the chain, consisting of the transitive closure of {name}`CoeOut` instances followed by {name}`CoeTC`.

 * {name}`CoeHTC` is the start of the chain, consisting of at most one {name}`CoeHead` instance followed by {name}`CoeOTC`.

 * {name}`CoeHTCT` is the whole chain, consisting of `CoeHTC` followed by at most one {name}`CoeTail` instance. Alternatively, it might be a {name}`NatCast` instance.

 * {name}`CoeT` represents the entire chain: it is either a {name}`CoeHTCT` chain or a single {name}`CoeDep` instance.

:::

:::figure "Auxiliary Classes for Coercions" (tag := "coe-aux-classes")
![A graphical representation of the relationships between the coercion transitive closure auxiliary classes](/static/figures/coe-chain.svg)
:::

{docstring CoeHTCT}

{docstring CoeHTC}

{docstring CoeOTC}

{docstring CoeTC}
