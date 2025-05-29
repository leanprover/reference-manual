import Lean
import Manual.ErrorExplanation

open Lean Meta

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

def outputDir := "explanation_mwes"

def main : IO UInt32 := do
  let out ← IO.Process.output {cmd := "lake", args := #["env", "which", "extract_explanation_example"]}
  throwIfNonzeroExit out "lake env which extract_explanation_example"
  -- Note: we can't use `withImports` because we need initializers
  let env ← importModules #[`Init] {}
  let explans := getErrorExplanationsRaw env
  for (name, explan) in explans do
    for h₁ : exIdx in [:explan.codeBlocks.size] do
      let blocks := explan.codeBlocks[exIdx].leanBlocks
      for h₂ : blockIdx in [:blocks.size] do
        let block := blocks[blockIdx]
        let blockName := ErrorExplanation.mkBlockName name exIdx blockIdx
        let some exePath := out.stdout.splitOn "\n" |>.head?
          | throw <| IO.userError "No executable path found"
        let exePath ← IO.FS.realPath exePath
        let childConfig := {
          cmd := "extract_explanation_example"
          args := #[outputDir, blockName]
          stdin := .piped, stdout := .piped, stderr := .piped
        }
        let out ← runWithStdin childConfig block
        throwIfNonzeroExit out s!"extract_explanation_example \"{blockName}\""
        let outPath := (outputDir : System.FilePath) / (blockName ++ ".json")
        -- Sanity-check that we did something:
        unless (← System.FilePath.pathExists outPath) do
          throw <| IO.userError s!"Failed to generate output file at {outPath}"

  return 0
