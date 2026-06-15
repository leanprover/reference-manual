/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lake.Toml.Decode
import Lake.Load.Toml

import Manual.Meta.LakeToml.Test

/-!
Shared `Manual.Toml.Test` instances for rendering an elaborated `Lake.Package` (and its constituent
configuration types) as the “expected elaboration result” shown in the manual.

These instances are factored out of `Manual.Meta.LakeToml` so that they can be reused both by the
`lakeToml`/`lakeLean` directives and by the standalone `extract-lakefile` executable, which
elaborates a Lean-format `lakefile.lean` in a subprocess and emits the formatted package.
-/

open Lean
open Std (Format)

namespace Manual

namespace Toml

instance [Test α] : Test (Lake.OrdNameMap α) where
  toString xs := Id.run do
    let mut out : Std.Format := Std.Format.nil
    for (k, v) in xs.toTreeMap do
      out := out ++ .group (.nest 2 <| Test.toString k ++ " ↦" ++ .line ++ Test.toString v) ++ "," ++ .line
    return .group (.nest 2 <| "{" ++ out) ++ "}"

instance [{n : Name} → Test (f n)] : Test (Lake.DNameMap f) where
  toString xs := Id.run do
    let mut out : Std.Format := Std.Format.nil
    for ⟨k, v⟩ in xs do
      out := out ++ .group (.nest 2 <| Test.toString k ++ " ↦" ++ .line ++ Test.toString v) ++ "," ++ .line
    return .group (.nest 2 <| "{" ++ out) ++ "}"



mutual

partial def testPatDescr [Test α] [Test β] : (Lake.PatternDescr α β) → Std.Format
  | .not x => .group <| .nest 2 <| ".not" ++ .line ++ testPat x
  | .coe x => .group <| .nest 2 <| ".coe" ++ .line ++ Test.toString x
  | .any xs => .group <| .nest 2 <| ".any" ++ .line ++ "#[" ++ arrElems (xs.map testPat) ++ "]"
  | .all xs => .group <| .nest 2 <| ".all" ++ .line ++ "#[" ++ arrElems (xs.map testPat) ++ "]"
where
  arrElems (xs : Array Std.Format) : Std.Format :=
    .group <| .nest 2 <| (Std.Format.text "," ++ .line).joinSep xs.toList

partial def testPat [Test α] [Test β] : (Lake.Pattern α β) → Std.Format
  | {filter, name, descr?} =>
    let fields : List Std.Format := [
      "filter :=" ++ .line ++ Test.toString filter,
      "name :=" ++ .line ++ Test.toString name,
      "descr? :=" ++ .line ++ Test.toString (descr?.map testPatDescr),
    ]
    .group <| (.nest 2 <| "{" ++ .line ++ (Std.Format.text "," ++ .line).joinSep fields) ++ "}"
end

instance [Test α] [Test β] : Test (Lake.PatternDescr α β) := ⟨testPatDescr⟩
instance [Test α] [Test β] : Test (Lake.Pattern α β) := ⟨testPat⟩

deriving instance Repr for Lake.StrPatDescr

instance : Test (Lake.Script) where
  toString s := s!"#<script {s.name}>"

instance : Test (Lake.ExternLibConfig n n') where
  toString _ := s!"#<extern lib>"

instance : Test (Lake.OpaqueTargetConfig n n') where
  toString _ := s!"#<opaque target>"

instance : Test (Lake.OpaquePostUpdateHook α) where
  toString _ := s!"#<post-update-hook>"

instance : Test Lake.Toml.DecodeError where
  toString
    | {ref, msg} => s!"{msg} at {ref}"

deriving instance Test for Lake.Dependency
deriving instance Test for Lake.PackageConfig
deriving instance Test for Lake.LeanLibConfig
deriving instance Test for Lake.LeanExeConfig

instance : Test (Lake.ConfigType kind pkg name) where
  toString :=
    match kind with
    | `lean_lib => fun (x : Lake.LeanLibConfig name) => Test.toString x
    | `lean_exe => fun (x : Lake.LeanExeConfig name) => Test.toString x
    | `extern_lib => fun (x : Lake.ExternLibConfig pkg name) => Test.toString x
    | .anonymous => fun (x : Lake.OpaqueTargetConfig pkg name) => Test.toString x
    | _ => fun _ => "Impossible!"

instance : Test Lake.CacheRef where
  toString _ := "#<cacheref>"

private def contains (fmt : Format) (c : Char) : Bool :=
  match fmt with
  | .text s => s.contains c
  | .tag _ x | .group x .. | .nest _ x => contains x c
  | .append x y => contains x c || contains y c
  | .align .. | .line | .nil => false

instance [Test α] : Test (Option α) where
  toString
    | none => "none"
    | some x =>
      let s := Test.toString x
      let s := if contains s '(' || contains s ' ' then "(" ++ s ++ ")" else s
      s!"some " ++ s

deriving instance Test for Lake.ConfigDecl
deriving instance Test for Lake.PConfigDecl
deriving instance Test for Lake.NConfigDecl

deriving instance Test for Lake.Package

end Toml

end Manual
