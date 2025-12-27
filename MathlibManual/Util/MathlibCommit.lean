/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jon Eugster
-/
import Lake.Load.Manifest
import Lean
import VersoManual

open Lean Verso.Doc.Elab

namespace MathlibManual

/-- Get Mathlib commit and create a link. -/
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
