/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Elab.Import
import Lake
open Lake DSL
open System (FilePath)

-- Using this assumes that each dependency has a tag of the form `v4.X.0`.
def leanVersion : String := s!"v{Lean.versionString}"
require "leanprover-community" / "mathlib" @ git leanVersion

require MD4Lean from git "https://github.com/acmepjz/md4lean"@"main"
require verso from git "https://github.com/leanprover/verso.git"@leanVersion
require «verso-manual» from git "https://github.com/leanprover/reference-manual.git"@leanVersion

package "mathlib-manual" where
  -- building the C code cost much more than the optimizations save
  -- In particular, the Localizer pass of LLVM takes tons of time (ca 90% for many chapters) and these flags disable it
  -- This is a circa 20% overall speedup (build and execute) at the time of writing
  moreLeancArgs := #["-O0", "-mllvm", "-fast-isel", "-mllvm", "-fast-isel-abort=0"]
  -- work around clang emitting invalid linker optimization hints that lld rejects
  moreLinkArgs :=
    if System.Platform.isOSX then
      #["-Wl,-ignore_optimization_hints"]
    else #[]

  leanOptions := #[⟨`weak.verso.code.warnLineLength, .ofNat 72⟩]

@[default_target]
lean_lib MathlibManual where
  leanOptions := #[
    ⟨`linter.all, false⟩
  ]


def figureDir : FilePath := "figures"
def figureOutDir : FilePath := "static/figures"
def errorExplanationExOutDir : FilePath :=
  defaultBuildDir / "error_explanation_examples"

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

/-
This section contains infrastructure for preprocessing code blocks in error explanations. Error
explanation code blocks must be allowed to contain imports, so we must run the full frontend over
each one. To improve efficiency, we do this in a preprocessing step in which code blocks with the
same imports are grouped together, avoiding the need to repeatedly import the same modules anew.

Preprocessing proceeds as follows:

1. Error explanations are extracted from the elaboration environment of this Lakefile (which
   matches the Lean version used to elaborate these examples in the manual itself) using the
   `all_error_explanations%` macro; we then extract any Lean code blocks these contain.
2. We group the extracted code blocks by their headers (`mkPreprocessingGroups`). We skip any code
   blocks for which there already exists a valid JSON file in the preprocessing output directory
   (determined by `hasUsableCache` by source hash and the Lean version used to generate the JSON).
3. The code blocks in each group are written to Lean modules in a temporary directory and
   preprocessed by the `extract_explanation_examples` tool (see `preprocessGroup`). Note that while
   we call this tool once for each preprocessing group, each code block gets a separate JSON output
   file (allowing us to cache on a per-code-block, rather than per-group, basis; this is especially
   important because the majority of the code blocks have no imports and thus belong to the same
   group).

To depend on the preprocessed JSON, modules can import `PreprocessedExplanations`, which depends on
this preprocessing target and exposes a constant `preprocessedExplanationsRoot` that gives the file
path to the directory to which the JSON files are written.
-/
section ExplanationPreprocessing

open Lean Meta

/- This must agree with `mkExampleName` in `Manual.ErrorExplanation`. -/
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
  let .ok version := json.getObjVal? "version" >>= Json.getStr?
    | return false
  return version == Lean.versionString && cacheHash == hash

/--
Runs the explanation example extractor over every entry in `examples`,
generating output JSON files in `explanationExamplesDir`. All entries in
`examples` must have equivalent headers, as the same environment will be reused
for each.
-/
def preprocessGroup (examples : Array (Name × String)) (exePath : FilePath) : IO Unit :=
  IO.FS.withTempDir fun tmpDir => do
    let examplePaths ← examples.mapM fun (name, input) => do
      let path := tmpDir / (name.toString ++ ".lean")
      IO.FS.writeFile path input
      pure path.toString
    let childConfig := {
      cmd := exePath.toString
      args := #[errorExplanationExOutDir.toString] ++ examplePaths
      stdin := .piped, stdout := .piped, stderr := .piped
    }
    let out ← IO.Process.output childConfig
    if out.exitCode != 0 then
      let args := childConfig.args.foldl (s!"{·} \"{·}\"") ""
      let cmd := s!"extract_explanation_examples{args}"
      throw <| IO.userError <|
        s!"Nonzero exit code {out.exitCode} when running `{cmd}`\n" ++
        s!"Stderr:\n{out.stderr}\n\nStdout:\n{out.stdout}\n\n"

deriving instance BEq, Hashable for Import

/--
Generates groups from `codeBlocks` of examples with equivalent headers,
discarding those that already have a valid cache.
-/
def mkPreprocessingGroups (codeBlocks : Array (Name × String)) :
    IO (Array (Array (Name × String))) := do
  let (map : Std.HashMap (Array Import) _) ←
    codeBlocks.foldlM (init := {}) fun acc (name, block) => do
      if (← hasUsableCache name.toString (hash block)) then
        pure acc
      else
        let inputCtx := Parser.mkInputContext block "Main.lean"
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
            -- Match MD4Lean by including the trailing newline:
            acc := acc.push ""
            let code := "\n".intercalate acc.toList
            codeBlocks := codeBlocks.push (mkExampleName exampleName idx, code)
            acc := #[]
            idx := idx + 1
        else
          acc := acc.push line
    else if state matches .insideCode true _ then
      acc := acc.push line
  return codeBlocks

deriving instance ToExpr for MessageSeverity
deriving instance ToExpr for ErrorExplanation.Metadata
deriving instance ToExpr for DeclarationLocation
deriving instance ToExpr for ErrorExplanation

/--
Elaborates to an expression containing all error explanation entries. This
provides access to error explanations outside of the metaprogramming monads.
-/
elab "all_error_explanations%" : term =>
  return toExpr <| getErrorExplanationsRaw (← getEnv)

/-- Preprocess code examples in error explanations. -/
target preprocess_explanations_async : Unit := do
  let exeJob ← extract_explanation_examples.fetch
  let explans := all_error_explanations%
  let allBlocks := explans.flatMap fun (name, explan) =>
    extractCodeBlocks name explan.doc
  let groups ← mkPreprocessingGroups allBlocks

  let writeModuleJob ← Job.async do
    let moduleSrc := s!"def preprocessedExplanationsRoot : System.FilePath :=\n  \
      \"{errorExplanationExOutDir}\"\n"
    let some mod ← findModule? `PreprocessedExplanations |
      error s!"Module `PreprocessedExplanations is missing from the Lake configuration"
    buildFileUnlessUpToDate' mod.leanFile do
      createParentDirs mod.leanFile
      IO.FS.writeFile mod.leanFile moduleSrc
      liftM (m := IO) <| try IO.FS.removeFile mod.oleanFile catch
        | .noFileOrDirectory .. => pure ()
        | e => throw e

  let preprocessJob ← exeJob.bindM fun exe => do
    let groupJobs ← groups.mapM (Job.async do preprocessGroup · exe)
    return Job.mixArray groupJobs

  return preprocessJob.mix writeModuleJob

/--
A blocking version of `preprocess_explanations_async`. Ensures that all required
files have been generated when `PreprocessedExplanations` is imported.
-/
target preprocess_explanations_sync : Unit := do
  .pure <$> (← preprocess_explanations_async.fetch).await

lean_lib PreprocessedExplanations where
  needs := #[preprocess_explanations_sync]
  srcDir := defaultBuildDir / "src"

end ExplanationPreprocessing

@[default_target]
lean_exe "generate-manual" where
  needs := #[`@/figures, `@/subversoExtractMod]
  root := `Main
