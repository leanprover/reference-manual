/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module
public import Verso
public import Verso.Doc.Elab.Monad
public import VersoManual.Basic
public meta import Verso.Doc.Elab.Inline

public section

namespace Manual

open Lean Elab
open Verso Doc Elab Genre.Manual

inline_extension Inline.title where
  traverse _ _ _ := pure none
  toTeX :=
    open Verso.Output.TeX in
    some <| fun goI _ _ content => do
      pure \TeX{\emph{\Lean{← content.mapM goI}}}
  toHtml :=
    open Verso.Output.Html in
    some <| fun goI _ _ content => do
      pure html%{<em class="work-title">{← content.mapM goI}</em>}

/--
Marks the title of a work, such as a paper or a book.

The title is rendered in italics.
The prose linter skips it.
-/
@[role]
meta def title : RoleExpanderOf Unit
  | (), inlines => do
    let content ← inlines.mapM elabInline
    ``(Verso.Doc.Inline.other Inline.title #[$content,*])
