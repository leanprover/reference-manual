/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module
public import SubVerso.Highlighting.Highlighted

public section


open Lean Elab
open SubVerso.Highlighting Highlighted


namespace Manual

namespace CommandSpec
mutual
  inductive Item where
    | metavar (name : String)
    | literalSyntax (string : String)
    | ellipses
    | optional (contents : List DecoratedItem)
    | or
  deriving ToJson, FromJson, Repr
  structure DecoratedItem where
    leading : String
    item : Item
    trailing : String
  deriving ToJson, FromJson, Repr
end

mutual
  partial def Item.toHighlighted : Item → Highlighted
    | .metavar x => .token ⟨.var ⟨x.toName⟩ x none, x⟩ -- Hack: abusing FVarId here
    | .literalSyntax s => .token ⟨.keyword none none none, s⟩
    | .ellipses => .token ⟨.unknown, "..."⟩
    | .or => .token ⟨.keyword none none none, "|"⟩
    | .optional xs =>
      .token ⟨.keyword none none none, "["⟩ ++
      .seq (xs.toArray.map DecoratedItem.toHighlighted) ++
      .token ⟨.keyword none none none, "]"⟩

  partial def DecoratedItem.toHighlighted : DecoratedItem → Highlighted
    | ⟨l, x, r⟩ => .text l ++ x.toHighlighted ++ .text r
end

open Syntax (mkCApp)

private def quoteList [Quote α `term] : List α → Term
  | []      => mkCIdent ``List.nil
  | (x::xs) => Syntax.mkCApp ``List.cons #[quote x, quoteList xs]

mutual
  partial def Item.quote : Item → Term
    | .metavar x => mkCApp ``Item.metavar #[Quote.quote x]
    | .literalSyntax s => mkCApp ``Item.literalSyntax #[Quote.quote s]
    | .ellipses => mkCApp ``Item.ellipses #[]
    | .or => mkCApp ``Item.or #[]
    | .optional xs =>
      have : Quote DecoratedItem := ⟨DecoratedItem.quote⟩
      mkCApp ``Item.optional #[quoteList xs]

  partial def DecoratedItem.quote : DecoratedItem → Term
    | ⟨l, i, t⟩ => mkCApp ``DecoratedItem.mk #[quote l, i.quote, quote t]
end

instance : Quote Item := ⟨Item.quote⟩
instance : Quote DecoratedItem := ⟨DecoratedItem.quote⟩

end CommandSpec


abbrev CommandSpec : Type := List CommandSpec.DecoratedItem

def CommandSpec.toHighlighted (spec : CommandSpec) : Highlighted := .seq (spec.map (·.toHighlighted)).toArray

declare_syntax_cat lake_cmd_spec_item
syntax ident : lake_cmd_spec_item
syntax str : lake_cmd_spec_item
syntax "..." : lake_cmd_spec_item
syntax "|" : lake_cmd_spec_item
syntax "[" lake_cmd_spec_item+ "]" : lake_cmd_spec_item

declare_syntax_cat lake_cmd_spec
syntax lake_cmd_spec_item* : lake_cmd_spec

mutual
  partial def CommandSpec.Item.ofSyntax (stx : TSyntax `lake_cmd_spec_item) : Except String CommandSpec.Item :=
    match stx with
    | `(lake_cmd_spec_item|$i:ident) => pure <| .metavar <| i.getId.toString (escape := false)
    | `(lake_cmd_spec_item|$s:str) => pure <| .literalSyntax s.getString
    | `(lake_cmd_spec_item|...) => pure <| .ellipses
    | `(lake_cmd_spec_item||) => pure <| .or
    | `(lake_cmd_spec_item|[ $items* ]) => .optional <$> items.toList.mapM DecoratedItem.ofSyntax
    | _ => .error s!"Not a command spec item: {stx}"

  partial def CommandSpec.DecoratedItem.ofSyntax
      (stx : TSyntax `lake_cmd_spec_item) : Except String CommandSpec.DecoratedItem := do
    return ⟨lead stx.raw.getHeadInfo, ← Item.ofSyntax stx, trail stx.raw.getTailInfo⟩
  where
    lead : SourceInfo → String
      | .original l .. => l.toString
      | _ => ""

    trail : SourceInfo → String
      | .original _ _ t _ => t.toString
      | _ => ""
end

def CommandSpec.ofSyntax (stx : Syntax) : Except String CommandSpec :=
  match stx with
  | `(lake_cmd_spec|$items:lake_cmd_spec_item*) => do
      items.toList.mapM DecoratedItem.ofSyntax
  | _ => .error s!"Not a command spec: {stx}"
