/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Data.Json
import Lean.Elab.InfoTree.Types

import Verso.Output.Html
import Verso.Output.TeX
import VersoManual

import Manual.Meta.Marginalia

namespace Manual

open Lean Elab
open Verso Doc Elab Html
open Verso.Output Html
open Verso.Genre Manual
open Verso.ArgParse

inductive Style where
  | textual
  | parenthetical
deriving ToJson, FromJson, Repr

inductive Month where
  | january | february | march | april
  | may | june | july | august
  | september | october | november | december
deriving ToJson, FromJson, DecidableEq, Ord, Repr

structure InProceedings where
  title : Doc.Inline Manual
  authors : Array (Doc.Inline Manual)
  year : Int
  booktitle : Doc.Inline Manual
  editors : Option (Array (Doc.Inline Manual)) := none
  series : Option (Doc.Inline Manual) := none
  url : Option String := none
deriving ToJson, FromJson, BEq, Hashable

structure Thesis where
  title : Doc.Inline Manual
  author : Doc.Inline Manual
  year : Int
  university : Doc.Inline Manual
  degree : Doc.Inline Manual
  url : Option String := none
deriving ToJson, FromJson, BEq, Hashable, Ord


section
attribute [local instance] Ord.arrayOrd
deriving instance Ord for InProceedings
end

inductive Citable where
  | inProceedings : InProceedings → Citable
  | thesis : Thesis → Citable
deriving ToJson, FromJson, BEq, Hashable, Ord

instance : Coe InProceedings Citable where
  coe := .inProceedings

instance : Coe Thesis Citable where
  coe := .thesis

def Citable.authors : Citable → Array (Doc.Inline Manual)
  | .inProceedings p => p.authors
  | .thesis p => #[p.author]

def Citable.title : Citable → Doc.Inline Manual
  | .inProceedings p => p.title
  | .thesis p => p.title

def Citable.year : Citable → Int
  | .inProceedings p => p.year
  | .thesis p => p.year

def Citable.url : Citable → Option String
  | .inProceedings p => p.url
  | .thesis p => p.url


private def slugString : Doc.Inline Manual → String
  | .text s | .code s | .math _ s => s
  | .bold i | .emph i | .concat i | .other _ i | .link i _ =>
    i.attach.map (fun ⟨x, _⟩ => slugString x) |>.foldr (init := "") (· ++ ·)
  | .linebreak .. | .image .. | .footnote .. => ""


def Citable.tag (c : Citable) : Slug :=
  c.authors.map (slugString) |>.foldr (init := s!"-{c.year}") (· ++ ·) |> .ofString

def Citable.sortKey (c : Citable) := c.authors.map slugString |>.foldr (init := s!" {c.year}") (· ++ ", " ++ ·)

private def andList (xs : Array Html) : Html :=
  if h : xs.size = 1 then xs[0]
  else
    open Html in
    (xs.extract 0 (xs.size - 2)).foldr (init := {{" and " {{xs.back}} }}) (· ++ ", " ++ ·)

partial def Bibliography.lastName (inl : Doc.Inline Manual) : Doc.Inline Manual :=
  let ws := words inl
  if _ : ws.size = 0 then inl
  else if _ : ws.size = 1 then ws[0]
  else Id.run do
    let mut lst := #[ws.back]
    let mut rest := ws.pop
    while rest.back?.isSome do
      let w := rest.back
      rest := rest.pop
      if parts.contains w then
        lst := lst.push w
        continue
      else
        break
    return .concat lst.reverse

where
  parts : List (Doc.Inline Manual) := ["de", "van", "la"].map .text

  words : Doc.Inline Manual → Array (Doc.Inline Manual)
  | .text str => str.splitOn " " |>.filter (· ≠ "") |>.toArray |>.map (.text)
  | .concat xs => xs.map words |>.foldl (init := #[]) (· ++ ·)
  | .linebreak .. => #[]
  | other => #[other]


def Citable.inlineHtml
    (go : Doc.Inline Genre.Manual → HtmlT Manual (ReaderT ExtensionImpls IO) Html)
    (p : Citable)
    (fmt : Style) :
    HtmlT Manual (ReaderT ExtensionImpls IO) Html :=
  open Html in do
    let authors ←
      if p.authors.size = 0 then
        pure {{""}}
      else if h : p.authors.size = 1 then
        go <| Bibliography.lastName p.authors[0]
      else if h : p.authors.size > 3 then
        (· ++ {{<em>"et al"</em>}}) <$> go (Bibliography.lastName p.authors[0])
      else andList <$> p.authors.mapM go
    -- TODO disambiguate when there are duplicate author/years
    -- TODO link to bibliography once it exists
    match fmt with
    | .textual =>
      return {{ {{authors}} s!" ({p.year})"}}
    | .parenthetical =>
      return {{" ("{{authors}} s!", {p.year})"}}

def Citable.bibHtml (go : Doc.Inline Genre.Manual → HtmlT Manual (ReaderT ExtensionImpls IO) Html) (c : Citable) : HtmlT Manual (ReaderT ExtensionImpls IO) Html := open Html in do
  match c with
  |  .inProceedings p =>
    let authors ← andList <$> p.authors.mapM go
    return {{ {{authors}} s!", {p.year}. " {{ link {{"“" {{← go p.title}} "”"}} }} ". In " <em>{{← go p.booktitle}}"."</em>{{(← p.series.mapM go).map ({{"(" {{·}} ")" }}) |>.getD .empty}} }}
  | .thesis p =>
    return {{ {{← go p.author}} s!", {p.year}. " <em>{{link (← go p.title)}}</em> ". " {{← go p.degree}} ", " {{← go p.university}} }}
where
  link (title : Html) : Html :=
    match c.url with
    | none => title
    | some u => {{<a href={{u}}>{{title}}</a>}}

def Inline.cite (citation : Citable) (style : Style := .parenthetical) : Inline where
  name := `Manual.citation
   -- The nested bit here _should_ be a no-op, but it's to avoid deserialization overhead during the traverse pass
  data := ToJson.toJson (ToJson.toJson citation, style)

structure CiteConfig where
  citation : Name

def CiteConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] [MonadFileMap m] : ArgParse m CiteConfig :=
  CiteConfig.mk <$> .positional `citation .resolvedName


@[role_expander citep]
def citep : RoleExpander
  | args, extra => do
    let config ← CiteConfig.parse.run args
    let x := mkIdent config.citation
    return #[← `(Doc.Inline.other (Inline.cite ($x : Citable) .parenthetical) #[$(← extra.mapM elabInline),*])]

@[role_expander citet]
def citet : RoleExpander
  | args, extra => do
    let config ← CiteConfig.parse.run args
    let x := mkIdent config.citation
    return #[← `(Doc.Inline.other (Inline.cite ($x : Citable) .textual) #[$(← extra.mapM elabInline),*])]

def citation := ()

@[inline_extension citation]
partial def cite.inlineDescr : InlineDescr where
  traverse _ data _ := do
    match FromJson.fromJson? data with
    | .error e => logError "Failed to deserialize citation"; return none
    | .ok (v : Json × Style) =>
      let cited : Option (Except String (Array Json)) := (← get).get? `Manual.Bibliography
      match cited with
      | .none =>
        modify (·.set `Manual.Bibliography (Json.arr #[v.1]))
      | .some (.error e) => logError e
      | .some (.ok citedSet) =>
        if citedSet.binSearchContains v.1 (cmp · · == .lt) then pure ()
        else modify (·.set `Manual.Bibliography <| citedSet.binInsert (cmp · · == .lt) v.1)
      pure none -- TODO disambiguate years
  toTeX := none
  extraCss := [Marginalia.css]
  toHtml :=
    open Verso.Output.Html in
    some <| fun go _ data _content => do -- TODO repurpose "content" for e.g. "page 5"
      match FromJson.fromJson? data with
      | .error e => HtmlT.logError s!"Failed to deserialize citation/style: {e}"; return {{""}}
      | .ok (v : Json × Style) =>
        match FromJson.fromJson? v.1 with
        | .error e => HtmlT.logError s!"Failed to deserialize citation: {e}"; return {{""}}
        | .ok (v' : Citable) =>
          let inl ← v'.inlineHtml go v.2
          let m ← v'.bibHtml go
          pure <| inl ++ Marginalia.html m
where
  cmp : Json → Json → Ordering
    | .null, .null => .eq
    | .null, _ => .lt
    | _, .null => .gt
    | .str s1, .str s2 => Ord.compare s1 s2
    | .str _, _ => .lt
    | _, .str _ => .gt
    | .num n1, .num n2 => Ord.compare n1 n2
    | .num _, _ => .lt
    | _, .num _ => .gt
    | .bool b1, .bool b2 => Ord.compare b1 b2
    | .bool _, _ => .lt
    | _, .bool _ => .gt
    | .arr a1, .arr a2 => (@Ord.arrayOrd _ ⟨cmp⟩).compare a1 a2
    | .arr _, _ => .lt
    | _, .arr _ => .gt
    | .obj o1, .obj o2 =>
      let inst1 : Ord String := inferInstance
      let inst2 : Ord Json := ⟨cmp⟩
      let inst : Ord (String × Json) := Ord.lex inst1 inst2
      let a1 := o1.toArray.map (fun x => (x.1, x.2)) |>.qsort (inst.compare · · == .lt)
      let a2 := o2.toArray.map (fun x => (x.1, x.2)) |>.qsort (inst.compare · · == .lt)
      (Ord.arrayOrd).compare a1 a2


-- TODO: Block-level element for the actual bibliography
