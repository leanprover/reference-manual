/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module
public import Manual.Meta.ModuleExample
import VersoManual.InlineLean -- shake: keep
public meta import Manual.Meta.ExpectString

public section

/-!
The `lakeSession` directive runs a sequence of commands against a project that is assembled in a
temporary directory at elaboration time.

A `lakeSession` directive may contain:

 * At most one configuration file: either a `toml` code block (written as `lakefile.toml`) or a
   `lean +lakefile` code block (written as `lakefile.lean`). A `toml` block marked `-show` is used
   but not rendered.
 * Any number of `lean (file := "Rel/Path.lean")` code blocks, written as source files. Each is
   elaborated after the commands have run, and its messages are reported at the corresponding
   lines of the block. A block marked `+error` is expected to produce at least one error.
 * Prose, in which `{name}` roles refer to names defined in the source files, as in
   `leanModules`.
 * Any number of `lakeCmd "…"` code blocks, run in order in the project directory. A command is
   expected to succeed (exit code `0`) unless it is marked `+error`, in which case it is expected to
   fail (any nonzero exit code). The block body is the expected command output, compared against the
   combined standard output and standard error of the command (an empty body asserts that there is
   no output). Output is normalized before comparison unless `+exact` is set. To run a command
   without checking its output, mark it `+ignoreOutput`; this requires an empty body. A command
   marked `-show` is run and checked but not rendered. A command may be a pipeline of stages
   separated by ` | `, which are run without a shell.

Other blocks (prose, ordinary `lean` examples, …) are otherwise rendered as-is.

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

meta def LakeSessionConfig.parse [Monad m] [MonadError m] : ArgParse m LakeSessionConfig :=
  LakeSessionConfig.mk <$> .flag `show true

/-- A source file to be written into the project. -/
private structure SourceFileConfig where
  file : String
  /-- Whether the file is expected to contain elaboration errors. -/
  error : Bool := false

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
  /-- Whether to render the command and its output, or only run and check it. -/
  «show» : Bool := true

section
variable [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m]

/--
Parse the arguments of a `lean` block inside a `lakeSession`: an optional `file` (marking it as a
source file), the `+lakefile` flag (marking it as the Lean-format configuration), and the `+error`
flag (marking a source file that is expected to fail to elaborate).
-/
private meta def leanBlockArgs : ArgParse m (Option String × Bool × Bool) :=
  (·, ·, ·) <$> .named `file .string true <*> .flag `lakefile false <*> .flag `error false

meta def LakeCmdConfig.parse : ArgParse m LakeCmdConfig :=
  LakeCmdConfig.mk <$> .positional `command .string <*>
    .flag `error false <*> .flag `exact false <*> .flag `ignoreOutput false <*> .flag `show true
end

private meta def isBlank (s : String) : Bool := s.all Char.isWhitespace

/-- The classification of a block inside a `lakeSession` directive. -/
private inductive SessionItem where
  /--
  A `toml` block, becoming `lakefile.toml`. The syntax is kept for rendering, which `-show`
  suppresses.
  -/
  | tomlConfig (contents : StrLit) (block : Syntax) («show» : Bool)
  /-- A `lean +lakefile` block, becoming `lakefile.lean`. The syntax is kept for rendering. -/
  | leanConfig (contents : StrLit) (block : Syntax)
  /-- A `lean (file := …)` source-file block. -/
  | source (cfg : SourceFileConfig) (contents : StrLit)
  /-- A `lakeCmd "…"` block, with its expected output and the block syntax (for error reporting). -/
  | command (cfg : LakeCmdConfig) (output : StrLit) (blame : Syntax)
  /-- Any other block, rendered unchanged. -/
  | passthrough (block : Syntax)

/-- Classify a block within a `lakeSession`. -/
private meta def classifySessionBlock (block : Syntax) : DocElabM SessionItem := do
  match block with
  | `(block| ``` toml $args* | $contents ```) =>
    let «show» ← (ArgParse.flag `show true).run (← parseArgs args)
    return .tomlConfig contents block «show»
  | `(block| ``` lakeCmd $args* | $output ```) =>
    let cfg ← LakeCmdConfig.parse.run (← parseArgs args)
    return .command cfg output block
  | `(block| ``` lean $args* | $contents ```) =>
    -- A `lean` block is the Lean-format configuration when marked `+lakefile`, a project source
    -- file when it carries a `file` argument, and otherwise an ordinary rendered example.
    match ← (try some <$> leanBlockArgs.run (← parseArgs args) catch _ => pure none) with
    | some (_, true, _) => return .leanConfig contents block
    | some (some file, false, error) => return .source ⟨file, error⟩ contents
    | _ => return .passthrough block
  | _ => return .passthrough block

/-- Drop a trailing build-timing annotation such as ` (1.3s)` or ` (320ms)` from a line. -/
private meta def stripTiming (line : String) : String :=
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

meta section

/--
Replace each mention of the project directory in `line` with `⟨project⟩`.

Tools may print the directory in its given form or with symbolic links resolved, so it is
recognized by its last two path components, and whatever precedes them up to the nearest
whitespace is elided along with them.
-/
private def elideProjectDir (projectDir : System.FilePath) (line : String) : String :=
  let suffix := "/" ++ (projectDir.parent >>= (·.fileName)).getD "" ++ "/" ++ projectDir.fileName.getD ""
  let parts := (line.splitOn suffix).toArray
  if parts.size ≤ 1 then line
  else Id.run do
    let mut out := ""
    for h : i in [0:parts.size] do
      let part := parts[i]
      if i + 1 < parts.size then
        let kept := String.ofList (part.toList.reverse.dropWhile (!·.isWhitespace)).reverse
        out := out ++ kept ++ "⟨project⟩"
      else
        out := out ++ part
    return out

/--
Replace each absolute path to one of the project's source files in `line` with the file's path
relative to `⟨project⟩`.

Build products restored from Lake's artifact cache can mention the directory of the build that
produced them rather than the current project directory, so source files are recognized by their
paths relative to the project, which are given in `files`.
-/
private def elideSourcePaths (files : Array String) (line : String) : String :=
  files.foldl (init := line) fun line file =>
    let parts := (line.splitOn ("/" ++ file)).toArray
    if parts.size ≤ 1 then line
    else Id.run do
      let mut out := parts[0]!
      for h : i in [1:parts.size] do
        let rest := parts[i]
        -- A mention ends the path: it is followed by a position, whitespace, or the end of the line.
        let ends := match rest.toList.head? with
          | none => true
          | some c => c == ':' || c.isWhitespace
        -- The path's directory is the text since the last whitespace.
        let rev := out.toList.reverse
        let dir := String.ofList (rev.takeWhile (!·.isWhitespace)).reverse
        if ends && dir.startsWith "/" then
          out := String.ofList (rev.dropWhile (!·.isWhitespace)).reverse ++ "⟨project⟩/" ++ file ++ rest
        else
          out := out ++ "/" ++ file ++ rest
      return out

/--
Normalize a line of command output: elide paths to the project's source files, the project
directory, and build timings.
-/
private def normalizeLine (projectDir : System.FilePath) (files : Array String) (line : String) :
    String :=
  elideProjectDir projectDir (elideSourcePaths files (stripTiming line))

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
  let out ← outputInterruptibly {cmd := "lake", args := #["env", "which", "subverso-extract-mod"]}
  if out.exitCode != 0 then
    throwError
      m!"When running 'lake env which subverso-extract-mod', the exit code was {out.exitCode}\n" ++
      m!"Stderr:\n{out.stderr}\n\nStdout:\n{out.stdout}\n\n"
  let some exe := out.stdout.splitOn "\n" |>.head?
    | throwError "No executable path found for 'subverso-extract-mod'"
  IO.FS.realPath exe

/-- The arguments for extracting the highlighting of module `modName` of the project in `dir`. -/
private def extractArgs
    (subverso : System.FilePath) (dir : System.FilePath) (modName : Name) :
    IO IO.Process.SpawnArgs := do
  return {
    cmd := toString subverso,
    args := #[modName.toString, (jsonFile dir modName).toString],
    cwd := some dir,
    env := #[
      ("LEAN_SRC_PATH", dir.toString ++ ((":" ++ ·) <$> (← IO.getEnv "LEAN_SRC_PATH")).getD ""),
      ("LEAN_PATH", (dir / ".lake" / "build" / "lib" / "lean").toString ++
        ((":" ++ ·) <$> (← IO.getEnv "LEAN_PATH")).getD "")
    ]
  }
where
  jsonFile (dir : System.FilePath) (modName : Name) : System.FilePath :=
    dir / (modName.toString : System.FilePath).addExtension "json"

/-- The highlighting extracted by a run of `extractArgs`, if it succeeded. -/
private def readHighlighting (dir : System.FilePath) (modName : Name) (out : IO.Process.Output) :
    IO (Option Highlighted) := do
  if out.exitCode != 0 then
    return none
  let json ← IO.FS.readFile (extractArgs.jsonFile dir modName)
  match Json.parse json >>= SubVerso.Module.Module.fromJson? with
  | .ok mod => return some (mod.items.foldl (init := .empty) fun hl v => hl ++ v.code)
  | .error _ => return none

/-- Locate the `extract-lakefile` executable in the current Lake workspace. -/
private def findExtractLakefile : DocElabM System.FilePath := do
  let out ← outputInterruptibly {cmd := "lake", args := #["env", "which", "extract-lakefile"]}
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
  let out ← outputInterruptibly {
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
    let subverso? ← if hasSources then some <$> findSubverso else pure none
    let extractLakefile? ← if cfg.show && hasLeanConfig then some <$> findExtractLakefile else pure none

    let rendered ← IO.FS.withTempDir fun dir => do
      let dir := dir / toString (← IO.monoMsNow)
      IO.FS.createDirAll dir

      let toolchain ← IO.FS.readFile "lean-toolchain"
      IO.FS.writeFile (dir / "lean-toolchain") toolchain

      -- Write the project files.
      for item in items do
        match item with
        | .tomlConfig contents _ _ =>
          IO.FS.writeFile (dir / "lakefile.toml") (← parserInputString contents)
        | .leanConfig contents _ =>
          IO.FS.writeFile (dir / "lakefile.lean") (← parserInputString contents)
        | .source cfg contents =>
          -- Source files are written verbatim, so command output refers to them as shown. Their
          -- elaboration messages are reported at the corresponding lines of this document below.
          let path := dir / (cfg.file : System.FilePath)
          path.parent.forM (IO.FS.createDirAll ·)
          IO.FS.writeFile path contents.getString
        | _ => pure ()

      -- Run the commands in order, validating each against its expectations.
      let files := items.filterMap fun | .source cfg _ => some cfg.file | _ => none
      for item in items do
        if let .command cfg output blame := item then
          runCommand dir files cfg output blame

      -- Elaborate each source file to obtain its highlighting and its messages.
      let mut highlights : Std.HashMap String Highlighted := {}
      if let some subverso := subverso? then
        -- The files' imports must be built before they can be elaborated.
        let out ← outputInterruptibly {
          cmd := "lake", args := #["build"], cwd := some dir
          -- `subverso-extract-mod` reads `.olean` files from the build directory, which the local artifact
          -- cache leaves empty unless artifacts are restored
          env := #[("LAKE_RESTORE_ARTIFACTS", "true")]
        }
        logBuild "lake build (for highlighting)" out
        let sources := items.filterMap fun | .source cfg contents => some (cfg, contents) | _ => none
        let outs ← outputsConcurrently (← sources.mapM fun (cfg, _) =>
          extractArgs subverso dir (fileToModule cfg.file))
        for ((cfg, contents), out) in sources.zip outs do
          if let some hl ← readHighlighting dir (fileToModule cfg.file) out then
            reportMessages cfg contents hl
            highlights := highlights.insert cfg.file (dropBlanks hl)
          else
            logErrorAt contents m!"Failed to elaborate '{cfg.file}'"
      let mut leanConfigHl : Option Highlighted := none
      if let some exe := extractLakefile? then
        leanConfigHl := (← extractLakefileHighlighting exe dir).map dropBlanks

      -- Render, preserving document order.
      if cfg.show then
        -- `{name}` roles in the surrounding prose refer to names defined in the source files.
        let allHl : Highlighted := highlights.fold (init := .empty) fun acc _ hl => acc ++ hl
        let prose := items.filterMap fun | .passthrough block => some block | _ => none
        let (prose, wrapNames) ← resolveNameRoles prose allHl
        let mut next := 0
        let mut resolved : Array SessionItem := #[]
        for item in items do
          if let .passthrough _ := item then
            resolved := resolved.push (.passthrough prose[next]!)
            next := next + 1
          else
            resolved := resolved.push item
        let items := resolved
        let body ← items.mapM (renderItem highlights leanConfigHl)
        pure #[← wrapNames (← `(Verso.Doc.Block.concat #[$body,*]))]
      else
        pure #[]

    if cfg.show then
      return rendered
    else
      return #[← ``(Verso.Doc.Block.empty)]

where
  /--
  Report the messages from elaborating a source file at the lines of the code block `block` that
  they belong to. Errors are reported as errors unless the file is marked `+error`, in which case
  they are expected, and an absence of errors is itself an error.
  -/
  reportMessages (cfg : SourceFileConfig) (block : StrLit) (hl : Highlighted) : DocElabM Unit := do
    let firstLine := ((← getFileMap).toPosition (block.raw.getPos?.getD 0)).line - 1
    let msgs := getMessages hl
    for (l, msg) in msgs do
      let stx ← lineStx (firstLine + l)
      match msg.severity with
      | .info => logSilentInfoAt stx msg.toString
      | .warning => logSilentAt stx .warning msg.toString
      | .error =>
        if cfg.error then logSilentAt stx .warning msg.toString
        else logErrorAt stx msg.toString
    if cfg.error && !msgs.any (·.2.severity == .error) then
      logErrorAt block m!"Error expected in '{cfg.file}', but none detected."

  /--
  Run a single command in `dir` and check its exit code and output. `files` are the paths of the
  project's source files, relative to `dir`.

  The command may be a pipeline of stages separated by ` | `. Each stage's standard output is the
  next stage's standard input. The pipeline's output is the last stage's standard output followed
  by every stage's standard error, and its exit code is that of the first stage that fails.
  -/
  runCommand (dir : System.FilePath) (files : Array String) (cfg : LakeCmdConfig) (output : StrLit)
      (blame : Syntax) : DocElabM Unit := do
    let mut input? : Option String := none
    let mut stderr := ""
    let mut exitCode : UInt32 := 0
    for stage in cfg.command.splitOn " | " do
      let parts := stage.splitOn " " |>.filter (!·.isEmpty)
      let some cmd := parts.head?
        | throwErrorAt blame "Empty command in '{cfg.command}'"
      let out ← outputInterruptibly (input? := input?) {
        cmd, args := parts.tail.toArray, cwd := some dir
        -- Later commands and highlighting extraction read build products from the build directory,
        -- which the local artifact cache leaves empty unless artifacts are restored
        env := #[("LAKE_RESTORE_ARTIFACTS", "true")]
      }
      logBuild stage out (some blame)
      input? := some out.stdout
      stderr := stderr ++ out.stderr
      if exitCode == 0 then exitCode := out.exitCode
    let out : IO.Process.Output := { exitCode, stdout := input?.getD "", stderr }

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
      let preEq := if cfg.exact then id else normalizeLine dir files
      -- The output is normalized before comparison, rather than only within it, so that the diff
      -- and the suggested replacement in a mismatch report are in terms of `⟨project⟩`.
      let combined := "\n".intercalate <| (out.stdout ++ out.stderr).splitOn "\n" |>.map preEq
      let useLine := if cfg.exact then (fun _ => true) else (fun l => !isBlank l && !isSetupNoise l)
      discard <| expectString s!"output of '{cfg.command}'" output combined
        (preEq := preEq) (useLine := useLine)

  /-- Render one classified block. -/
  renderItem (highlights : Std.HashMap String Highlighted) (leanConfigHl : Option Highlighted)
      (item : SessionItem) : DocElabM Term := do
    match item with
    | .tomlConfig _ block «show» =>
      unless «show» do return ← ``(Verso.Doc.Block.empty)
      -- Re-render the original `toml` block for highlighting. Its only argument is `show`, which
      -- is dropped so that the renderer does not see it.
      -- The original block's name is reused, since a `toml` written in a quotation is hygienic.
      let `(block| ``` $name:ident $_* | $contents ```) := block
        | elabBlock ⟨block⟩
      elabBlock ⟨← `(block| ``` $name:ident | $contents ```)⟩
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
      unless cfg.show do return ← ``(Verso.Doc.Block.empty)
      let body ← parserInputString output
      let text := "$ " ++ cfg.command ++ (if isBlank body then "" else "\n" ++ body)
      ``(Verso.Doc.Block.code $(quote text))
    | .passthrough block =>
      elabBlock ⟨block⟩
