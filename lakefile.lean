/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Elab.Import
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
def errorExplanationExOutDir : FilePath := "error_explanation_examples"

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


lean_exe extract_explanation_examples where
  root := `ExtractExplanationExamples
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

section ExplanationPreprocessing
open Lean Meta

/- This must agree with `DiagnosticExplanation.mkExampleName`. -/
private def mkExampleName (errorName : Name) (idx : Nat) : Name :=
  errorName ++ s!"block{idx}".toName

/--
Returns `true` if there exists a cached elaboration result for code block `id`
with hash `hash` on the current Lean version.
-/
def hasUsableCache (id : String) (hash : UInt64) : IO Bool := do
  let path := errorExplanationExOutDir / (id ++ ".json")
  unless (← System.FilePath.pathExists path) do return false
  let cacheStr ← IO.FS.readFile path
  let .ok json := Json.parse cacheStr | return false
  let .ok cacheHash := json.getObjVal? "hash" >>= FromJson.fromJson? (α := UInt64)
    | return false
  let .ok version := json.getObjVal? "toolchain" >>= Json.getStr?
    | return false
  return version == Lean.versionString && cacheHash == hash

/--
Runs the explanation example extractor over every entry in `examples`,
generating output JSON files in `explanationExamplesDir`. All entries in
`examples` must have equivalent headers, as the same environment will be reused
for each.
-/
def processImportGroup (examples : Array (Name × String)) (exePath : FilePath) (outDir : FilePath) : IO Unit :=
  IO.FS.withTempDir fun tmpDir => do
    let examplePaths ← examples.mapM fun (name, input) => do
      let path := tmpDir / (name.toString ++ ".lean")
      IO.FS.writeFile path input
      pure path.toString
    let childConfig := {
      cmd := exePath.toString
      args := #[outDir.toString] ++ examplePaths
      stdin := .piped, stdout := .piped, stderr := .piped
    }
    let out ← IO.Process.output childConfig
    if out.exitCode != 0 then
      let args := childConfig.args.foldl (s!"{·} \"{·}\"") ""
      let cmd := s!"extract_explanation_example{args}"
      throw <| IO.userError <|
        s!"When running `{cmd}`, the exit code was {out.exitCode}\n" ++
        s!"Stderr:\n{out.stderr}\n\nStdout:\n{out.stdout}\n\n"

deriving instance BEq, Hashable for Import

/-- Generates groups from `codeBlocks` of examples with equivalent headers. -/
def groupByImports (codeBlocks : Array (Name × String)) :
    IO (Array (Array (Name × String))) := do
  let (map : Std.HashMap (Array Import) _) ←
    codeBlocks.foldlM (init := {}) fun acc (name, block) => do
      if (← hasUsableCache name.toString (hash block)) then pure ()
      let inputCtx := Parser.mkInputContext block "<input>"
      let (header, _, _) ← Parser.parseHeader inputCtx
      let imports := Elab.headerToImports header
      let acc := if acc.contains imports then acc else acc.insert imports #[]
      pure <| acc.modify imports fun namedBlocks => namedBlocks.push (name, block)
  return map.toArray.map Prod.snd

/-- The state of a Markdown traversal: are we inside or outside a code block? -/
inductive MDTraversalState where
  | outsideCode
  | insideCode (isLean : Bool) (numTicks : Nat)

/--
Extracts Lean code blocks from `input` and returns them with their indexed names.
-/
def extractCodeBlocks (exampleName : Name) (input : String) : Array (Name × String) := Id.run do
  let lines := input.splitOn "\n"
  let mut codeBlocks : Array (Name × String) := #[]

  let mut state := MDTraversalState.outsideCode
  let mut acc : Array String := #[]
  let mut idx := 0
  for line in lines do
    if line.startsWith "```" then
      let numTicks := line.takeWhile (· == '`') |>.length
      match state with
      | .outsideCode =>
        let lang := line.drop numTicks |>.takeWhile (! ·.isWhitespace)
        state := .insideCode (lang == "lean" || lang.isEmpty) numTicks
      | .insideCode isLean expectedTicks =>
        if numTicks == expectedTicks then
          state := .outsideCode
          if isLean then
            let code := "\n".intercalate acc.toList
            codeBlocks := codeBlocks.push (mkExampleName exampleName idx, code)
            acc := #[]
            idx := idx + 1
    else if state matches .insideCode true _ then
      acc := acc.push line
  return codeBlocks

/-- Preprocess code examples in error explanations. -/
target error_explanations : Array Name := Job.async do
  let pkg ← getRootPackage
  let .some exe := pkg.findLeanExe? `extract_explanation_examples |
    Lake.logError "Could not find `extract_explanation_examples` executable. \
      Run `lake build extract_explanation_examples` to build it."
    failure
  let env ← importModules #[`Lean.ErrorExplanations] {} (loadExts := true)
  let explans := getErrorExplanationsRaw env
  let allBlocks := explans.flatMap fun (name, explan) =>
    extractCodeBlocks name explan.doc
  let groups ← groupByImports allBlocks
  for group in groups do
    processImportGroup group exe.file errorExplanationExOutDir
  return allBlocks.map (·.1)

end ExplanationPreprocessing

@[default_target]
lean_exe "generate-manual" where
  needs := #[`@/extract_explanation_example, `@/figures, `@/subversoExtractMod]
  root := `Main
