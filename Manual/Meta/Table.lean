/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import Lean.Elab.InfoTree.Types

import Manual.Meta.Figure

open Verso Doc Elab
open Verso.Genre Manual
open Verso.ArgParse

open Lean Elab

set_option pp.rawOnError true

namespace Manual

def Block.table (columns : Nat) (header : Bool) (name : Option String) : Block where
  name := `Manual.table
  data := ToJson.toJson (columns, header, name, (none : Option Tag))

structure TableConfig where
  /-- Name for refs -/
  name : Option String := none
  header : Bool := false


def TableConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] [MonadFileMap m] : ArgParse m TableConfig :=
  TableConfig.mk <$> .named `tag .string true <*> ((·.getD false) <$> .named `header .bool true)

@[directive_expander table]
def table : DirectiveExpander
  | args, contents => do
    let cfg ← TableConfig.parse.run args
    -- The table should be a list of lists. Extract them!
    let #[oneBlock] := contents
      | throwError "Expected a single unordered list"
    let `(block|ul{$items*}) := oneBlock
      | throwErrorAt oneBlock "Expected a single unordered list"
    let preRows ← items.mapM getLi
    let rows ← preRows.mapM fun blks => do
      let #[oneInRow] := blks.filter (·.raw.isOfKind ``Verso.Syntax.ul)
        | throwError "Each row should have exactly one list in it"
      let `(block|ul{ $cellItems*}) := oneInRow
        | throwErrorAt oneInRow "Each row should have exactly one list in it"
      cellItems.mapM getLi
    if h : rows.size = 0 then
      throwErrorAt oneBlock "Expected at least one row"
    else
      let columns := rows[0].size
      if columns = 0 then
        throwErrorAt oneBlock "Expected at least one column"
      if rows.any (·.size != columns) then
        throwErrorAt oneBlock s!"Expected all rows to have same number of columns, but got {rows.map (·.size)}"

      let flattened := rows.flatten
      let blocks : Array (Syntax.TSepArray `term ",") ← flattened.mapM (·.mapM elabBlock)
      pure #[← ``(Block.other (Block.table $(quote columns) $(quote cfg.header) $(quote cfg.name)) #[Block.ul #[$[Verso.Doc.ListItem.mk #[$blocks,*]],*]])]

where
  getLi
    | `(list_item| * $content* ) => pure content
    | other => throwErrorAt other "Expected list item"


@[block_extension table]
def table.descr : BlockDescr where
  traverse id data contents := do
    match FromJson.fromJson? data (α := Nat × Bool × Option String × Option Tag) with
    | .error e => logError s!"Error deserializing table data: {e}"; pure none
    | .ok (_, _, none, _) => pure none
    | .ok (c, hdr, some x, none) =>
      let path ← (·.path) <$> read
      let tag ← Verso.Genre.Manual.externalTag id path x
      pure <| some <| Block.other {Block.table c hdr none with id := some id, data := toJson (c, some x, some tag)} contents
    | .ok (_, _, some _, some _) => pure none
  toTeX := none
  toHtml :=
    open Verso.Doc.Html in
    open Verso.Output.Html in
    some <| fun goI goB id data blocks => do
      match FromJson.fromJson? data (α := Nat × Bool × Option String × Option Tag) with
      | .error e =>
        HtmlT.logError s!"Error deserializing table data: {e}"
        return .empty
      | .ok (columns, header, _, _) =>
      if let #[.ul items] := blocks then
        let xref ← HtmlT.state
        let attrs := xref.htmlId id
        let mut items := items
        let mut rows := #[]
        while items.size > 0 do
          rows := rows.push (items.take columns |>.map (·.contents))
          items := items.extract columns items.size

        return {{
          <table class="tabular" {{attrs}}>
            {{← rows.mapIdxM fun i r => do
              let cols ← Output.Html.seq <$> r.mapM fun c => do
                let cell : Output.Html ← c.mapM goB
                if header && i == 0 then
                  pure {{<th>{{cell}}</th>}}
                else
                  pure {{<td>{{cell}}</td>}}
              pure {{<tr>{{cols}}</tr>}}
            }}
          </table>
        }}

      else
        HtmlT.logError "Malformed table"
        return .empty
  extraCss := [
r##"
table.tabular {
  margin: auto;
  border-spacing: 1rem;
}
table.tabular td, table.tabular th {
  text-align: left;
  vertical-align: top;
}
table.tabular td > p:first-child, table.tabular th > p:first-child {
  margin-top: 0;
}
table.tabular td > p:last-child, table.tabular th > p:first-child {
  margin-bottom: 0;
}
"##
  ]
