/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
-- TODO: this should end up in Lean
import Manual.ErrorExplanation
import Lake
open Lake DSL
open System (FilePath)

require MD4Lean from git "https://github.com/acmepjz/md4lean"@"main"
require verso from git "https://github.com/leanprover/verso.git"@"nightly-testing"

package "verso-manual" where
  -- building the C code cost much more than the optimizations save
  moreLeancArgs := #["-O0"]
  -- work around clang emitting invalid linker optimization hints that lld rejects
  moreLinkArgs :=
    if System.Platform.isOSX then
      #["-Wl,-ignore_optimization_hints"]
    else #[]

  leanOptions := #[⟨`weak.verso.code.warnLineLength, .ofNat 72⟩]

lean_lib Manual where


def figureDir : FilePath := "figures"
def figureOutDir : FilePath := "static/figures"
def codeExamplesDir : FilePath := "explanation_mwes"

def ensureDir (dir : System.FilePath) : IO Unit := do
  if !(← dir.pathExists) then
    IO.FS.createDirAll dir
  if !(← dir.isDir) then
    throw (↑ s!"Not a directory: {dir}")

/-- Ensure that the subverso-extract-mod executable is available -/
target subversoExtractMod : FilePath := do
  let some pkg := ← findPackage? `subverso
    | failure
  let some exe := pkg.findLeanExe? `«subverso-extract-mod»
    | failure
  exe.fetch


lean_exe extract_explanation_example where
  root := `ExtractExample
  supportInterpreter := true


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

open Lean
def ErrorExplanation.mkBlockName (explanationName : Name) (exampleIdx : Nat) (blockIdx : Nat) :=
  s!"{explanationName}-example{exampleIdx}-block{blockIdx}"

def Lean.ErrorExplanation.CodeBlockSet.leanBlocks (blocks : CodeBlockSet) : Array String :=
  #[blocks.broken] ++ blocks.fixedWithOutputs.map Prod.fst

open IO Process in
/-- A duplicate of `IO.Process.output` that passes a string via stdin. -/
def runWithStdin (args : SpawnArgs) (input : String) : IO Output := do
  let child ← spawn { args with stdout := .piped, stderr := .piped, stdin := .piped }
  child.stdin.putStrLn input
  child.stdin.flush
  let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait
  let stdout ← IO.ofExcept stdout.get
  pure { exitCode := exitCode, stdout := stdout, stderr := stderr }

def throwIfNonzeroExit (out : IO.Process.Output) (cmd : String) : IO Unit := do
  if out.exitCode != 0 then
    throw <| IO.userError <|
      s!"When running `{cmd}`, the exit code was {out.exitCode}\n" ++
      s!"Stderr:\n{out.stderr}\n\nStdout:\n{out.stdout}\n\n"

def preprocessExplanations (exePath : FilePath) : IO Unit := do
  -- let out ← IO.Process.output {cmd := "lake", args := #["env", "which", "extract_explanation_example"]}
  -- throwIfNonzeroExit out "lake env which extract_explanation_example"
  -- Note: we can't use `withImports` because we need initializers
  let env ← importModules #[`Init] {}
  let explans := getErrorExplanationsRaw env
  for (name, explan) in explans do
    for h₁ : exIdx in [:explan.codeBlocks.size] do
      let blocks := explan.codeBlocks[exIdx].leanBlocks
      for h₂ : blockIdx in [:blocks.size] do
        let block := blocks[blockIdx]
        let blockName := ErrorExplanation.mkBlockName name exIdx blockIdx
        -- let some exePath := out.stdout.splitOn "\n" |>.head?
        --   | throw <| IO.userError "No executable path found"
        -- let exePath ← IO.FS.realPath exePath
        let childConfig := {
          cmd := exePath.toString
          args := #[codeExamplesDir.toString, blockName]
          stdin := .piped, stdout := .piped, stderr := .piped
        }
        let out ← runWithStdin childConfig block
        throwIfNonzeroExit out s!"extract_explanation_example \"{blockName}\""
        let outPath := codeExamplesDir / (blockName ++ ".json")
        -- Sanity-check that we did something:
        unless (← System.FilePath.pathExists outPath) do
          throw <| IO.userError s!"Failed to generate output file at {outPath}"


target preprocess_explanations : Unit := do
  let pkg ← getRootPackage
  let .some exe := pkg.findLeanExe? `extract_explanation_example
    | failure
  preprocessExplanations exe.file
  -- TODO: not clear what this should actually return
  return pure ()

@[default_target]
lean_exe "generate-manual" where
  needs := #[`@/extract_explanation_example, `@preprocess_explanations, `@/figures, `@/subversoExtractMod]
  root := `Main
