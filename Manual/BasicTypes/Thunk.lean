/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Verso.Genre Manual InlineLean

set_option pp.rawOnError true

#doc (Manual) "Lazy Computations" =>
%%%
tag := "Thunk"
%%%

A {deftech}_thunk_ delays the computation of a value.
In particular, the {name}`Thunk` type is used to delay the computation of a value in compiled code until it is explicitly requested—this request is called {deftech key:="force"}_forcing_ the thunk.
The computed value is saved, so subsequent requests do not result in recomputation.
Computing values at most once, when explicitly requested, is called {deftech}_lazy evaluation_.{index}[call-by-need]
This caching is invisible to Lean's logic, in which {name}`Thunk` is equivalent to a function from {name}`Unit`.


# Logical Model
%%%
tag := "Thunk-model"
%%%

Thunks are modeled as a single-field structure that contains a function from {lean}`Unit`.
The structure's field is private, so the function itself cannot be directly accessed.
Instead, {name}`Thunk.get` should be used.
From the perspective of the logic, they are equivalent; {name}`Thunk.get` exists to be overridden in the compiler by the platform primitive that implements lazy evaluation.

{docstring Thunk}

# Runtime Representation
%%%
tag := "Thunk-runtime"
%%%

:::figure "Memory layout of thunks" (tag := "thunkffi")
![Memory layout of thunks](/static/figures/thunk.svg)
:::

Thunks are one of the primitive object types supported by the Lean runtime.
The object header contains a specific tag that indicates that an object is a thunk.

:::paragraph
Thunks have two fields:
 * `m_value` is a pointer to a saved value, which is a null pointer if the value has not yet been computed.
 * `m_closure` is a closure which is to be called when the value should be computed.

The runtime system maintains the invariant that either the closure or the saved value is a null pointer.
If both are null pointers, then the thunk is being forced on another thread.
:::

When a thunk is {tech key:="force"}[forced], the runtime system first checks whether the saved value has already been computed, returning it if so.
Otherwise, it attempts to acquire a lock on the closure by atomically swapping it with a null pointer.
If the lock is acquired, it is invoked to compute the value; the computed value is stored in the saved value field and the reference to the closure is dropped.
If not, then another thread is already computing the value; the system waits until it is computed.

# Coercions
%%%
tag := "Thunk-coercions"
%%%

:::leanSection
```lean (show := false)
variable {α : Type u} {e : α}
```
There is a coercion from any type {lean}`α` to {lean}`Thunk α` that converts a term {lean}`e` into {lean}`Thunk.mk fun () => e`.
Because the elaborator {ref "coercion-insertion"}[unfolds coercions], evaluation of the original term {lean}`e` is delayed; the coercion is not equivalent to {name}`Thunk.pure`.
:::

:::example "Lazy Lists"

Lazy lists are lists that may contain thunks.
The {name LazyList.delayed}`delayed` constructor causes part of the list to be computed on demand.
```lean
inductive LazyList (α : Type u) where
  | nil
  | cons : α → LazyList α → LazyList α
  | delayed : Thunk (LazyList α) → LazyList α
deriving Inhabited
```

Lazy lists can be converted to ordinary lists by forcing all the embedded thunks.
```lean
def LazyList.toList : LazyList α → List α
  | .nil => []
  | .cons x xs => x :: xs.toList
  | .delayed xs => xs.get.toList
```

Many operations on lazy lists can be implemented without forcing the embedded thunks, instead building up further thunks.
The body of {name LazyList.delayed}`delayed` does not need to be an explicit call to {name}`Thunk.mk` because of the coercion.
```lean
def LazyList.take : Nat → LazyList α → LazyList α
  | 0, _ => .nil
  | _, .nil => .nil
  | n + 1, .cons x xs => .cons x <| .delayed <| take n xs
  | n + 1, .delayed xs => .delayed <| take (n + 1) xs.get

def LazyList.ofFn (f : Fin n → α) : LazyList α :=
  Fin.foldr n (init := .nil) fun i xs =>
    .delayed <| LazyList.cons (f i) xs

def LazyList.append (xs ys : LazyList α) : LazyList α :=
  .delayed <|
    match xs with
    | .nil => ys
    | .cons x xs' => LazyList.cons x (append xs' ys)
    | .delayed xs' => append xs'.get ys
```

Laziness is ordinarily invisible to Lean programs: there is no way to check whether a thunk has been forced.
However, {keywordOf Lean.Parser.Term.dbgTrace}`dbg_trace` can be used to gain insight into thunk evaluation.
```lean
def observe (tag : String) (i : Fin n) : Nat :=
  dbg_trace "{tag}: {i.val}"
  i.val
```

The lazy lists {lean}`xs` and {lean}`ys` emit traces when evaluated.
```lean
def xs := LazyList.ofFn (n := 3) (observe "xs")
def ys := LazyList.ofFn (n := 3) (observe "ys")
```

Converting {lean}`xs` to an ordinary list forces all of the embedded thunks:
```lean (name := lazy1)
#eval xs.toList
```
```leanOutput lazy1
xs: 0
xs: 1
xs: 2
```
```leanOutput lazy1
[0, 1, 2]
```

Likewise, converting {lean}`xs.append ys` to an ordinary list forces the embedded thunks:
```lean (name := lazy2)
#eval xs.append ys |>.toList
```
```leanOutput lazy2
xs: 0
xs: 1
xs: 2
ys: 0
ys: 1
ys: 2
```
```leanOutput lazy2
[0, 1, 2, 0, 1, 2]
```

Appending {lean}`xs` to itself before forcing the thunks results in a single set of traces, because each thunk's code is evaluated just once:
```lean (name := lazy3)
#eval xs.append xs |>.toList
```
```leanOutput lazy3
xs: 0
xs: 1
xs: 2
```
```leanOutput lazy3
[0, 1, 2, 0, 1, 2]
```

Finally, taking a prefix of {lean}`xs.append ys` results in only some of the thunks in {lean}`ys` being evaluated:
```lean (name := lazy4)
#eval xs.append ys |>.take 4 |>.toList
```
```leanOutput lazy4
xs: 0
xs: 1
xs: 2
ys: 0
```
```leanOutput lazy4
[0, 1, 2, 0]
```
:::


# API Reference
%%%
tag := "Thunk-api"
%%%

{docstring Thunk.get}

{docstring Thunk.map}

{docstring Thunk.pure}

{docstring Thunk.bind}
