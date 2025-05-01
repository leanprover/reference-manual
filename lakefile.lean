/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lake
open Lake DSL
open System (FilePath)

require verso from git "https://github.com/leanprover/verso.git"@"v4.19.0"

package "verso-manual" where
  -- building the C code cost much more than the optimizations save
  moreLeancArgs := #["-O0"]
  -- work around clang emitting invalid linker optimization hints that lld rejects
  moreLinkArgs :=
    if System.Platform.isOSX then
      #["-Wl,-ignore_optimization_hints"]
    else #[]


lean_lib Manual where


def figureDir : FilePath := "figures"
def figureOutDir : FilePath := "static/figures"

def ensureDir (dir : System.FilePath) : IO Unit := do
  if !(← dir.pathExists) then
    IO.FS.createDirAll dir
  if !(← dir.isDir) then
    throw (↑ s!"Not a directory: {dir}")

/-- Ensure that the subverso-extract-mod executable is available -/
target subversoExtractMod : FilePath := do
  if let some pkg := ← findPackage? `subverso then
    if let some exe := pkg.findLeanExe? `«subverso-extract-mod» then
      exe.fetch
    else
      failure
  else
    failure


target figures : Array FilePath := do
  let files := (← figureDir.readDir).filterMap fun f => do
    let some "tex" := f.path.extension | throw ()
    let some fn := f.path.fileName | throw ()
    -- Ignore backup files
    if ".#".isPrefixOf fn then throw ()
    return f.path

  let files := files.qsort (toString · < toString ·)
  let srcs := Job.collectArray (← liftM <| files.mapM inputTextFile)
  let traceFile := figureDir.join "lake.trace"
  srcs.mapM fun srcInfo => do
    buildUnlessUpToDate traceFile (← getTrace) traceFile do
      for src in srcInfo do
        let some f := src.fileStem
          | continue
        proc { cmd := "lualatex", args := #[f], cwd := some figureDir} (quiet := true)
        proc { cmd := "lualatex", args := #[f], cwd := some figureDir} (quiet := true)
        proc { cmd := "lualatex", args := #[f], cwd := some figureDir} (quiet := true)
        proc { cmd := "lualatex", args := #[f], cwd := some figureDir} (quiet := true)
        proc { cmd := "pdftocairo", args := #["-svg", s!"{f}.pdf", s!"{f}.svg"], cwd := some figureDir} (quiet := true)

        ensureDir "static"
        ensureDir figureOutDir
        for fmt in ["pdf", "svg"] do
          let built := s!"{f}.{fmt}"
          IO.println s!"Generated: {figureOutDir.join built}"
          IO.FS.withFile (figureDir.join built) .read fun h =>
            IO.FS.withFile (figureOutDir.join built) .write fun h' => do
              let mut buf ← h.read 1024
              while !buf.isEmpty do
                h'.write buf
                buf ← h.read 1024

    pure srcInfo

@[default_target]
lean_exe "generate-manual" where
  needs := #[`@/figures, `@/subversoExtractMod]
  root := `Main
