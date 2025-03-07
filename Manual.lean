/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoManual
import Std

import Manual.Tactics
import Manual.Guides

import Lake.CLI.Main

open Verso.Genre Manual

set_option pp.rawOnError true
namespace Manual

open Lean Verso.Doc.Elab
/--
Display the time the manual was built in the verso text.
TODO: move this to a better place.
-/
@[role_expander now]
def now : RoleExpander
  | #[], #[] => do
    let now := (← Std.Time.ZonedDateTime.now) |>.format "uuuu-MM-dd HH:mm (ZZ)"
    pure #[← ``(Verso.Doc.Inline.text $(quote now))]
  | _, _ => throwError "Unexpected arguments"

/--
Get Mathlib commit and create a link
TODO: move this to a better place.
-/
@[role_expander mathlibCommit]
def mathlibCommit : RoleExpander
  | #[], #[] => do
    let manifest ← Lake.Manifest.load "lake-manifest.json"
    let some pkg ← pure <| manifest.packages.find? fun (pkg : Lake.PackageEntry) => pkg.name == `mathlib
      | throwError "Couldn't read Mathlib commit hash from lake-manifest.json!"
    let (commit, url) ← match pkg.src with
      | .git url rev _ _ =>
        pure (rev.take 7, s!"{url}/commits/{rev}")
      | _ => throwError "expected Mathlib to be required from git"
    pure #[← ``(Verso.Doc.Inline.link $(quote #[← ``(Verso.Doc.Inline.text $(quote commit))]) $(quote url))]
  | _, _ => throwError "Unexpected arguments"

end Manual

#doc (Manual) "Mathlib Manual" =>
%%%
tag := "mathlib-manual"
%%%

This document has been last updated at **{now}[]** using Lean **{versionString}[]** and Mathlib commit {mathlibCommit}[].

**Other resources**:
- [Mathlib Documentation](https://leanprover-community.github.io/mathlib4_docs/index.html):
  automatically generated collection of all declarations from Mathlib.
- The [Lean Language Reference](https://lean-lang.org/doc/reference/latest/) contains
  detailed information about Lean Code.

If you would like to contribute content, please create a PR using the two github links
at the bottom left of this page!

{include 0 Manual.Tactics}

{include 0 Manual.Guides}
