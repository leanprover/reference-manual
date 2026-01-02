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
open Verso.Genre.Manual.InlineLean

section

open Lean Elab Command

/- Needed due to big infotree coming out of the instance quotation in the example here -/
set_option maxRecDepth 1024
set_option maxHeartbeats 650_000

/-- Classes that are part of the manual, not to be shown -/
-- TODO: When moving to v4.26.0-rc1, @kim-em removed `Plausible.Arbitrary` from this list.
-- Should it be restored?
private def hiddenDerivable : Array Name := #[``Manual.Toml.Test]

private def derivableClasses : IO (Array Name) := do
  let handlers ← derivingHandlersRef.get
  let derivable :=
    handlers.toList.map (·.fst)
      |>.toArray
      |>.filter (fun x => !hiddenDerivable.contains x && !(`Lean).isPrefixOf x)
      |>.qsort (·.toString < ·.toString)
  pure derivable

private def checkDerivable (expected : Array Name) : CommandElabM Unit := do
  let classes ← derivableClasses
  let extra := classes.filter (· ∉ expected)
  let missing := expected.filter (· ∉ classes)
  if extra.isEmpty && missing.isEmpty then
    Verso.Log.logSilentInfo m!"Derivable classes match!"
  else
    unless extra.isEmpty do
      logError
        m!"These classes were not expected. If they should appear in the list here, \
           then add them to the call; otherwise, add them to `{.ofConstName ``hiddenDerivable}`: \
           {.andList <| extra.toList.map (.ofConstName ·)}"
    unless missing.isEmpty do
      logError
        m!"These classes were expected but not present. Check whether the text needs updating, then \
           remove them from the call."

end


#eval checkDerivable #[``BEq, ``DecidableEq, ``Hashable, ``Inhabited, ``Nonempty, ``Ord, ``Repr, ``SizeOf, ``TypeName, ``LawfulBEq, ``ReflBEq]

open Verso Doc Elab ArgParse in
open Lean in
open SubVerso Highlighting in
@[directive_expander derivableClassList]
def derivableClassList : DirectiveExpander
  | args, contents => do
    -- No arguments!
    ArgParse.done.run args
    if contents.size > 0 then throwError "Expected empty directive"
    let classNames ← derivableClasses
    let itemStx ← classNames.mapM fun n => do
      let hl : Highlighted ← constTok n n.toString
      `(Inline.other {Verso.Genre.Manual.InlineLean.Inline.name with data := ToJson.toJson $(quote hl)} #[Inline.code $(quote n.toString)])
    let theList ← `(Verso.Doc.Block.ul #[$[⟨#[Verso.Doc.Block.para #[$itemStx]]⟩],*])
    return #[theList]

open Lean Elab Command

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

```imports -show
import Lean.Elab
```

Instances of the {name}`IsEnum` class demonstrate that a type is a finite enumeration by providing a bijection between the type and a suitably-sized {name}`Fin`:
```lean
class IsEnum (α : Type) where
  size : Nat
  toIdx : α → Fin size
  fromIdx : Fin size → α
  to_from_id : ∀ (i : Fin size), toIdx (fromIdx i) = i
  from_to_id : ∀ (x : α), fromIdx (toIdx x) = x
```

For inductive types that are trivial enumerations, where no constructor expects any parameters, instances of this class are quite repetitive.
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
