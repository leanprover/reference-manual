/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Elab.Import
import Lake
open Lake DSL
open System (FilePath)

require versowebcomponents from git "https://github.com/leanprover/verso-web-components"@"main"
require illuminate from git "https://github.com/leanprover/illuminate"@"main"
require verso from git "https://github.com/leanprover/verso.git"@"nightly-testing"


package "verso-manual" where
  -- building the C code cost much more than the optimizations save
  moreLeancArgs := #["-O0"]
  -- work around clang emitting invalid linker optimization hints that lld rejects
  moreLinkArgs :=
    if System.Platform.isOSX then
      #["-Wl,-ignore_optimization_hints"]
    else #[]

  leanOptions := #[
    ⟨`weak.verso.code.warnLineLength, .ofNat 72⟩,
    ⟨`weak.linter.typography.dashes, true⟩,
    ⟨`weak.linter.typography.quotes, true⟩,
    ⟨`weak.linter.typ, .ofNat 72⟩
  ]

-- Extended examples used in the grind chapter
@[default_target]
lean_lib IndexMap where
  srcDir := "extended-examples"

@[default_target]
lean_lib IndexMapGrind where
  srcDir := "extended-examples"

@[default_target]
lean_lib Manual where

/-- Ensure that the subverso-extract-mod executable is available -/
target subversoExtractMod : FilePath := do
  let some pkg := ← findPackageByName? `subverso
    | failure
  let some exe := pkg.findLeanExe? `«subverso-extract-mod»
    | failure
  exe.fetch

@[default_target]
lean_exe "generate-manual" where
  needs := #[`@/subversoExtractMod]
  root := `Main

@[default_target]
lean_lib Tutorial where

@[default_target]
lean_exe "generate-tutorials" where
  root := `TutorialMain

def lakeExe (prog : String) (args : Array String) : IO Unit := do
  IO.println s!"Running {prog} with args {args}"
  -- Using spawn and wait here causes the process to inherit stdio streams from Lake, so output is immediately visible
  let code ← IO.Process.Child.wait <| (← IO.Process.spawn { cmd := "lake", args := #["--quiet", "exe", prog] ++ args })
  if code ≠ 0 then
    let code' := code.toUInt8
    let code := if code' ≠ 0 then code' else 1
    IO.eprintln s!"Failed to run {prog} with args {args}"
    IO.Process.exit code
