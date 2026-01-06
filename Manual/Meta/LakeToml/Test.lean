/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Elab.Command
import Lean.Elab.Deriving

namespace Manual.Toml

open Std (Format)
open Lean Elab

/-- Types that can be used in tests embedded in the manual for TOML decoding -/
class Test (α : Sort u) where
  toString : α → Format

instance {p : Prop} : Test p where
  toString _ := .text "…"

instance [ToString α] : Test α where
  toString := .text ∘ toString

instance [Repr α] : Test α where
  toString x := repr x

instance [Test α] : Test (Array α) where
  toString arr := "#[" ++ .group (.nest 2 <| Format.joinSep (arr.map Test.toString).toList ("," ++ .line))  ++ "]"

instance [Test α] : Test (NameMap α) where
  toString xs := "{" ++ .group (.nest 2 <| Format.joinSep (xs.toList.map (fun x => s!"'{x.1}' ↦ {Test.toString x.2}")) ("," ++ .line)) ++ "}"

instance {α : Type u} {β : Type v} : Test (α → β) where
  toString _ := "#<fun>"

-- HACK: elide these fields that are platform-specific
def ignoreFields := [`buildArchive]

open Lean Elab Command in
def deriveTest (declNames : Array Name) : CommandElabM Bool := do
  if h : declNames.size ≠ 1 then return false
  else
    let declName := declNames[0]
    if !isStructure (← getEnv) declName then
      throwError "Can't derive 'Test' for non-structure '{declName}'"
    let params ← liftTermElabM do
      let uniParams ← (← getEnv).find? declName |>.mapM (Meta.mkFreshLevelMVarsFor ·)
      let ty ← Meta.inferType (.const declName <| uniParams.getD [])
      Meta.forallTelescopeReducing ty fun params ret =>
        pure <| params.mapIdx fun i _ => s!"x{i}".toName
    let fs := getStructureFields (← getEnv) declName
    let fieldBinds ← fs.mapM fun f =>
      `(Lean.Parser.Term.structInstField|$(mkIdent f):ident := $(mkIdent f))
    let header : Term := Syntax.mkApp (mkIdent declName) (params.map (mkIdent ·))
    let fields : TSyntaxArray `term ← fs.mapM fun f => do
      let rhs ← if f ∈ ignoreFields then pure (quote "ELIDED") else `(Test.toString $(mkIdent f))
      `(Format.group <| Format.nest 2 <|
        Format.text $(quote <| toString f ++ " :=") ++ Format.line ++
        $rhs)

    let cmd ←
      `(instance : Test $header where
          toString
            | ⟨$(fs.map mkIdent),*⟩ => "{" ++ .group (.nest 2 <| (Format.text "," ++ .line).joinSep [$fields,*]) ++ "}")

    elabCommand cmd
    return true

initialize
  registerDerivingHandler ``Test deriveTest
