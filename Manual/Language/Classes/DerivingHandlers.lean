/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta


open Manual
open Verso.Genre
open Verso.Genre.Manual


open Lean Elab Command

/- Needed due to big infotree coming out of the instance quotation in the example here -/
set_option maxHeartbeats 1000000
set_option maxRecDepth 1024

def derivableClasses : IO (Array Name) := do
  let handlers ← derivingHandlersRef.get
  let derivable := handlers.toList.map (·.fst) |>.toArray |>.qsort (·.toString < ·.toString)
  pure derivable

open Verso Doc Elab ArgParse in
open SubVerso Highlighting in
@[directive_expander derivableClassList]
def derivableClassList : DirectiveExpander
  | args, contents => do
    -- No arguments!
    ArgParse.done.run args
    if contents.size > 0 then throwError "Expected empty directive"
    let classNames ← derivableClasses
    let itemStx ← classNames.filter (!(`Lean).isPrefixOf ·) |>.mapM fun n => do
      let hl : Highlighted ← constTok n n.toString
      `(Inline.other {_root_.Manual.Inline.name with data := ToJson.toJson $(quote hl)} #[Inline.code $(quote n.toString)])
    let theList ← `(Verso.Doc.Block.ul #[$[⟨0, #[Verso.Doc.Block.para #[$itemStx]]⟩],*])
    return #[theList]

#doc (Manual) "Deriving Handlers" =>
%%%
tag := "deriving-handlers"
%%%

Instance deriving uses a table of {deftech}_deriving handlers_ that maps type class names to metaprograms that derive instances for them.
Deriving handlers may be added to the table using {lean}`registerDerivingHandler`, which should be called in an {keywordOf Lean.Parser.Command.initialize}`initialize` block.
Each deriving handler should have the type {lean}`Array Name → CommandElabM Bool`.
When a user requests that an instance of a class be derived, its registered handlers are called one at a time.
They are provided with all of the names in the mutual block for which the instance is to be derived, and should either correctly derive an instance and return {lean}`true` or have no effect and return {lean}`false`.
When a handler returns {lean}`true`, no further handlers are called.

Lean includes deriving handlers for the following classes:
:::derivableClassList
:::

{docstring Lean.Elab.registerDerivingHandler}


::::keepEnv
:::example "Deriving Handlers"
Instances of the {name}`IsEnum` class demonstrate that a type is a finite enumeration by providing a bijection between the type and a suitably-sized {name}`Fin`:
```lean
class IsEnum (α : Type) where
  size : Nat
  toIdx : α → Fin size
  fromIdx : Fin size → α
  to_from_id : ∀ (i : Fin size), toIdx (fromIdx i) = i
  from_to_id : ∀ (x : α), fromIdx (toIdx x) = x
```

For datatypes that are trivial enumerations, where no constructor expects any parameters, instances of this class are quite repetitive.
The instance for `Bool` is typical:
```lean
instance : IsEnum Bool where
  size := 2
  toIdx
    | false => 0
    | true => 1
  fromIdx
    | 0 => false
    | 1 => true
  to_from_id
    | 0 => rfl
    | 1 => rfl
  from_to_id
    | false => rfl
    | true => rfl
```

The deriving handler programmatically constructs each pattern case, by analogy to the {lean}`IsEnum Bool` implementation:
```lean
open Lean Elab Parser Term Command

def deriveIsEnum (declNames : Array Name) : CommandElabM Bool := do
  if h : declNames.size = 1 then
    let env ← getEnv
    if let some (.inductInfo ind) := env.find? declNames[0] then
      let mut tos : Array (TSyntax ``matchAlt) := #[]
      let mut froms := #[]
      let mut to_froms := #[]
      let mut from_tos := #[]
      let mut i := 0

      for ctorName in ind.ctors do
        let c := mkIdent ctorName
        let n := Syntax.mkNumLit (toString i)

        tos      := tos.push      (← `(matchAltExpr| | $c => $n))
        from_tos := from_tos.push (← `(matchAltExpr| | $c => rfl))
        froms    := froms.push    (← `(matchAltExpr| | $n => $c))
        to_froms := to_froms.push (← `(matchAltExpr| | $n => rfl))

        i := i + 1

      let cmd ← `(instance : IsEnum $(mkIdent declNames[0]) where
                    size := $(quote ind.ctors.length)
                    toIdx $tos:matchAlt*
                    fromIdx $froms:matchAlt*
                    to_from_id $to_froms:matchAlt*
                    from_to_id $from_tos:matchAlt*)
      elabCommand cmd

      return true
  return false

initialize
  registerDerivingHandler ``IsEnum deriveIsEnum
```
:::
::::
