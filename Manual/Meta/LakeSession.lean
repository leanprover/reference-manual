/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Elab.Command

import Verso
import Verso.Doc.ArgParse
import Verso.Doc.Elab.Monad
import VersoManual

import SubVerso.Module

import Manual.Meta.Basic
import Manual.Meta.ExpectString
import Manual.Meta.ModuleExample

/-!
The `lakeSession` directive runs a sequence of commands against a project that is assembled in a
temporary directory at elaboration time.

A `lakeSession` directive may contain:

 * At most one configuration file: either a `toml` code block (written as `lakefile.toml`) or a
   `lean +lakefile` code block (written as `lakefile.lean`).
 * Any number of `lean (file := "Rel/Path.lean")` code blocks, written as source files.
 * Any number of `lakeCmd "…"` code blocks, run in order in the project directory. A command is
   expected to succeed (exit code `0`) unless it is marked `+error`, in which case it is expected to
   fail (any nonzero exit code). The block body is the expected command output, compared against the
   combined standard output and standard error of the command (an empty body asserts that there is
   no output). Output is normalized before comparison unless `+exact` is set. To run a command
   without checking its output, mark it `+ignoreOutput`; this requires an empty body.

Other blocks (prose, ordinary `lean` examples, …) are rendered as-is.

With `-show`, the directive runs and validates everything but renders nothing, which is useful for
built-in tests that are not user-facing examples.
-/

open Verso ArgParse Doc Elab Genre.Manual
open Verso.Doc.Elab
open Verso.Log
open Lean Elab
open scoped Lean.Doc.Syntax
open SubVerso.Highlighting (Highlighted)

namespace Manual

/-- Options for the `lakeSession` directive. -/
structure LakeSessionConfig where
  /-- Whether to render the session, or only run it for its side effects (validation). -/
  «show» : Bool

def LakeSessionConfig.parse [Monad m] [MonadError m] : ArgParse m LakeSessionConfig :=
  LakeSessionConfig.mk <$> .flag `show true

/-- A source file to be written into the project. -/
structure SourceFileConfig where
  file : String

/-- A single command to run, together with its expectations. -/
structure LakeCmdConfig where
  /-- The command line. -/
  command : String
  /-- Whether the command is expected to fail (exit with a nonzero code) rather than succeed. -/
  error : Bool := false
  /-- Whether to compare output verbatim instead of normalizing it. -/
  exact : Bool := false
  /-- Whether to skip checking the output entirely. Requires an empty code block. -/
  ignoreOutput : Bool := false

section
variable [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m]

/--
Parse the arguments of a `lean` block inside a `lakeSession`: an optional `file` (marking it as a
source file) and the `+lakefile` flag (marking it as the Lean-format configuration).
-/
def leanBlockArgs : ArgParse m (Option String × Bool) :=
  (·, ·) <$> .named `file .string true <*> .flag `lakefile false

def LakeCmdConfig.parse : ArgParse m LakeCmdConfig :=
  LakeCmdConfig.mk <$> .positional `command .string <*>
    .flag `error false <*> .flag `exact false <*> .flag `ignoreOutput false
end

private def isBlank (s : String) : Bool := s.all Char.isWhitespace

/-- The classification of a block inside a `lakeSession` directive. -/
inductive SessionItem where
  /-- A `toml` block, becoming `lakefile.toml`. The syntax is kept for rendering. -/
  | tomlConfig (contents : StrLit) (block : Syntax)
  /-- A `lean +lakefile` block, becoming `lakefile.lean`. The syntax is kept for rendering. -/
  | leanConfig (contents : StrLit) (block : Syntax)
  /-- A `lean (file := …)` source-file block. -/
  | source (cfg : SourceFileConfig) (contents : StrLit)
  /-- A `lakeCmd "…"` block, with its expected output and the block syntax (for error reporting). -/
  | command (cfg : LakeCmdConfig) (output : StrLit) (blame : Syntax)
  /-- Any other block, rendered unchanged. -/
  | passthrough (block : Syntax)

/-- Classify a block within a `lakeSession`. -/
def classifySessionBlock (block : Syntax) : DocElabM SessionItem := do
  match block with
  | `(block| ``` toml $_* | $contents ```) => return .tomlConfig contents block
  | `(block| ``` lakeCmd $args* | $output ```) =>
    let cfg ← LakeCmdConfig.parse.run (← parseArgs args)
    return .command cfg output block
  | `(block| ``` lean $args* | $contents ```) =>
    -- A `lean` block is the Lean-format configuration when marked `+lakefile`, a project source
    -- file when it carries a `file` argument, and otherwise an ordinary rendered example.
    match ← (try some <$> leanBlockArgs.run (← parseArgs args) catch _ => pure none) with
    | some (_, true) => return .leanConfig contents block
    | some (some file, false) => return .source ⟨file⟩ contents
    | _ => return .passthrough block
  | _ => return .passthrough block

/-- Drop a trailing build-timing annotation such as ` (1.3s)` or ` (320ms)` from a line. -/
private def stripTiming (line : String) : String :=
  match line.splitOn " (" with
  | [] | [_] => line
  | parts =>
    if isTiming parts[parts.length - 1]! then
      " (".intercalate parts.dropLast
    else line
where
  isTiming (seg : String) : Bool :=
    seg.endsWith "s)" &&
    (let inner := (seg.dropEnd 2).copy
     !inner.isEmpty && inner.all (fun c => c.isDigit || c == '.' || c == 'm'))

/-- Normalize a line of command output: elide the project directory and build timings. -/
private def normalizeLine (projectDir : String) (line : String) : String :=
  (stripTiming line).replace projectDir "⟨project⟩"

private def containsStr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

/--
Whether a line is noise produced only because the project lives in a fresh temporary directory (and
so would not be seen by a reader running the same command in an established project).
-/
private def isSetupNoise (line : String) : Bool :=
  containsStr line "no previous manifest, creating one from scratch" ||
  containsStr line "toolchain not updated; already up-to-date"

/-- Convert a relative source-file path such as `Foo/Bar.lean` to the module name `Foo.Bar`. -/
private def fileToModule (file : String) : Name :=
  let noExt := (file.toSlice.dropSuffix ".lean").copy
  noExt.splitOn "/" |>.foldl (init := Name.anonymous) fun n s => n.str s

/-- Locate the `subverso-extract-mod` executable in the current Lake workspace. -/
private def findSubverso : DocElabM System.FilePath := do
  let out ← IO.Process.output {cmd := "lake", args := #["env", "which", "subverso-extract-mod"]}
  if out.exitCode != 0 then
    throwError
      m!"When running 'lake env which subverso-extract-mod', the exit code was {out.exitCode}\n" ++
      m!"Stderr:\n{out.stderr}\n\nStdout:\n{out.stdout}\n\n"
  let some exe := out.stdout.splitOn "\n" |>.head?
    | throwError "No executable path found for 'subverso-extract-mod'"
  IO.FS.realPath exe

/-- Extract highlighting for a single already-built module, or `none` if extraction fails. -/
private def extractHighlighting
    (subverso : System.FilePath) (dir : System.FilePath) (modName : Name) :
    DocElabM (Option Highlighted) := do
  let jsonFile := dir / (modName.toString : System.FilePath).addExtension "json"
  let out ← IO.Process.output {
    cmd := toString subverso,
    args := #[modName.toString, jsonFile.toString],
    cwd := some dir,
    env := #[
      ("LEAN_SRC_PATH", dir.toString ++ ((":" ++ ·) <$> (← IO.getEnv "LEAN_SRC_PATH")).getD ""),
      ("LEAN_PATH", (dir / ".lake" / "build" / "lib" / "lean").toString ++
        ((":" ++ ·) <$> (← IO.getEnv "LEAN_PATH")).getD "")
    ]
  }
  if out.exitCode != 0 then
    return none
  let json ← IO.FS.readFile jsonFile
  match Json.parse json >>= SubVerso.Module.Module.fromJson? with
  | .ok mod => return some (mod.items.foldl (init := .empty) fun hl v => hl ++ v.code)
  | .error _ => return none

/-- Locate the `extract-lakefile` executable in the current Lake workspace. -/
private def findExtractLakefile : DocElabM System.FilePath := do
  let out ← IO.Process.output {cmd := "lake", args := #["env", "which", "extract-lakefile"]}
  if out.exitCode != 0 then
    throwError
      m!"When running 'lake env which extract-lakefile', the exit code was {out.exitCode}\n" ++
      m!"Stderr:\n{out.stderr}\n\nStdout:\n{out.stdout}\n\n"
  let some exe := out.stdout.splitOn "\n" |>.head?
    | throwError "No executable path found for 'extract-lakefile'"
  IO.FS.realPath exe

/-- Extract highlighting for the Lean-format `lakefile.lean`, or `none` if extraction fails. -/
private def extractLakefileHighlighting (exe dir : System.FilePath) :
    DocElabM (Option Highlighted) := do
  let jsonFile := dir / "lakefile.json"
  let out ← IO.Process.output {
    cmd := toString exe,
    args := #[(dir / "lakefile.lean").toString, jsonFile.toString],
    cwd := some dir
  }
  if out.exitCode != 0 then
    return none
  let json ← IO.FS.readFile jsonFile
  let some moduleJson := Json.parse json |>.toOption.bind (·.getObjVal? "module" |>.toOption)
    | return none
  match SubVerso.Module.Module.fromJson? moduleJson with
  | .ok mod => return some (mod.items.foldl (init := .empty) fun hl v => hl ++ v.code)
  | .error _ => return none

@[directive_expander lakeSession]
def lakeSession : DirectiveExpander
  | args, contents => do
    let cfg ← LakeSessionConfig.parse.run args
    let items ← contents.mapM classifySessionBlock

    let configs := items.filter fun | .tomlConfig .. | .leanConfig .. => true | _ => false
    if configs.size > 1 then
      throwError "Expected at most one configuration file \
        (a 'toml' block or a 'lean +lakefile' block), got {configs.size}"

    let hasSources := items.any fun | .source .. => true | _ => false
    let hasLeanConfig := items.any fun | .leanConfig .. => true | _ => false
    let subverso? ← if cfg.show && hasSources then some <$> findSubverso else pure none
    let extractLakefile? ← if cfg.show && hasLeanConfig then some <$> findExtractLakefile else pure none

    let rendered ← IO.FS.withTempDir fun dir => do
      let dir := dir / toString (← IO.monoMsNow)
      IO.FS.createDirAll dir

      let toolchain ← IO.FS.readFile "lean-toolchain"
      IO.FS.writeFile (dir / "lean-toolchain") toolchain

      -- Write the project files.
      for item in items do
        match item with
        | .tomlConfig contents _ =>
          IO.FS.writeFile (dir / "lakefile.toml") (← parserInputString contents)
        | .leanConfig contents _ =>
          IO.FS.writeFile (dir / "lakefile.lean") (← parserInputString contents)
        | .source cfg contents =>
          let path := dir / (cfg.file : System.FilePath)
          path.parent.forM (IO.FS.createDirAll ·)
          IO.FS.writeFile path (← parserInputString contents)
        | _ => pure ()

      -- Run the commands in order, validating each against its expectations.
      for item in items do
        if let .command cfg output blame := item then
          runCommand dir cfg output blame

      -- Extract highlighting, but only when rendering.
      let mut highlights : Std.HashMap String Highlighted := {}
      if let some subverso := subverso? then
        -- Source files must be built before their highlighting can be extracted.
        let out ← IO.Process.output {cmd := "lake", args := #["build"], cwd := some dir}
        logBuild "lake build (for highlighting)" out
        for item in items do
          if let .source cfg _ := item then
            if let some hl ← extractHighlighting subverso dir (fileToModule cfg.file) then
              highlights := highlights.insert cfg.file (dropBlanks hl)
      let mut leanConfigHl : Option Highlighted := none
      if let some exe := extractLakefile? then
        leanConfigHl := (← extractLakefileHighlighting exe dir).map dropBlanks

      -- Render, preserving document order.
      if cfg.show then
        items.mapM (renderItem highlights leanConfigHl)
      else
        pure #[]

    if cfg.show then
      return rendered
    else
      return #[← ``(Verso.Doc.Block.empty)]
where
  /-- Run a single command in `dir` and check its exit code and output. -/
  runCommand (dir : System.FilePath) (cfg : LakeCmdConfig) (output : StrLit) (blame : Syntax) :
      DocElabM Unit := do
    let parts := cfg.command.splitOn " " |>.filter (!·.isEmpty)
    let some cmd := parts.head?
      | throwErrorAt blame "Empty command"
    let out ← IO.Process.output {
      cmd, args := parts.tail.toArray, cwd := some dir
    }
    logBuild cfg.command out (some blame)

    let exitOk := if cfg.error then out.exitCode != 0 else out.exitCode == 0
    unless exitOk do
      let expected := if cfg.error then m!"a nonzero exit code" else m!"exit code 0"
      logErrorAt blame
        m!"Expected '{cfg.command}' to exit with {expected}, but it exited with \
          {out.exitCode}.\nStdout:\n{out.stdout}\nStderr:\n{out.stderr}"

    let body ← parserInputString output
    if cfg.ignoreOutput then
      unless isBlank body do
        logErrorAt blame
          m!"With '+ignoreOutput', the code block must be empty, but it contains output."
    else
      let combined := out.stdout ++ out.stderr
      let preEq := if cfg.exact then id else normalizeLine dir.toString
      let useLine := if cfg.exact then (fun _ => true) else (fun l => !isBlank l && !isSetupNoise l)
      discard <| expectString s!"output of '{cfg.command}'" output combined
        (preEq := preEq) (useLine := useLine)

  /-- Render one classified block. -/
  renderItem (highlights : Std.HashMap String Highlighted) (leanConfigHl : Option Highlighted)
      (item : SessionItem) : DocElabM Term := do
    match item with
    | .tomlConfig _ block =>
      -- Re-render the original `toml` block for highlighting.
      elabBlock ⟨block⟩
    | .leanConfig contents _ =>
      match leanConfigHl with
      | some hl =>
        ``(Verso.Doc.Block.other (Verso.Genre.Manual.InlineLean.Block.lean $(quote hl)) #[])
      | none =>
        ``(Verso.Doc.Block.code $(quote (← parserInputString contents)))
    | .source cfg contents =>
      match highlights[cfg.file]? with
      | some hl =>
        ``(Verso.Doc.Block.other (Verso.Genre.Manual.InlineLean.Block.lean $(quote hl)) #[])
      | none =>
        ``(Verso.Doc.Block.code $(quote (← parserInputString contents)))
    | .command cfg output _ =>
      let body ← parserInputString output
      let text := "$ " ++ cfg.command ++ (if isBlank body then "" else "\n" ++ body)
      ``(Verso.Doc.Block.code $(quote text))
    | .passthrough block =>
      elabBlock ⟨block⟩
