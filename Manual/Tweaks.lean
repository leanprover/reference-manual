import VersoManual
import Std
import Lean
import Lake

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option maxRecDepth 1024

open Lean Verso.Doc.Elab

namespace Manual


#check Std.Time.ZonedDateTime.now

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
