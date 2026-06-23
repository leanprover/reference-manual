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
The `lakeLean` directive, the Lean-format counterpart to `lakeToml`.

Like `lakeToml`, it takes a configuration code block together with an `expected` code block that
contains the elaborated `Lake.Package`. Unlike `lakeToml`, the configuration is a Lean-format
`lakefile.lean`, which cannot be decoded in-process: it imports `Lake` and uses the package
configuration DSL. It is therefore elaborated by the `extract-lakefile` executable in a subprocess,
which emits both the elaborated package (for validation against the `expected` block) and the
SubVerso highlighting of the source (for display).
-/

open Verso ArgParse Doc Elab Genre.Manual
open Verso.Log
open Lean Elab
open scoped Lean.Doc.Syntax

namespace Manual

structure LakeLeanOpts where
  /-- Whether to display the highlighted configuration, or only validate it. -/
  «show» : Bool

def LakeLeanOpts.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] :
    ArgParse m LakeLeanOpts :=
  LakeLeanOpts.mk <$> ((·.getD true) <$> .named `show .bool true)

/--
Renders a Lean-format `lakefile.lean` together with its elaborated `Lake.Package` configuration.

The directive expects exactly one `lean` code block, containing the configuration, and exactly one
`expected` code block, containing the elaborated package as formatted by the `extract-lakefile`
executable. The configuration is elaborated, the result is checked against the `expected` block, and
(unless `show` is `false`) the highlighted configuration is displayed.
-/
@[directive_expander lakeLean]
def lakeLean : DirectiveExpander
  | args, contents => do
    let opts ← LakeLeanOpts.parse.run args
    let (expected, contents) := contents.partition fun
      | `(block| ``` expected | $_ ```) => true
      | _ => false
    let leanBlocks := contents.filterMap fun
      | `(block| ``` lean $_* | $leanStr ```) => some leanStr
      | _ => none

    if h : expected.size ≠ 1 then
      throwError "Expected exactly 1 'expected' code block, got {expected.size}"
    else if h : leanBlocks.size ≠ 1 then
      throwError "Expected exactly 1 'lean' code block, got {leanBlocks.size}"
    else
      let `(block| ```expected | $expectedStr ```) := expected[0]
        | throwErrorAt expected[0] "Expected an 'expected' code block with no arguments"
      let leanStr := leanBlocks[0]

      let exe ← findExtractLakefile
      let (package, hl) ← IO.FS.withTempDir fun dir => do
        let dir := dir / toString (← IO.monoMsNow)
        IO.FS.createDirAll dir
        let lakefile := dir / "lakefile.lean"
        IO.FS.writeFile lakefile (← parserInputString leanStr)
        let jsonFile := dir / "lakefile.json"
        let out ← IO.Process.output {
          cmd := toString exe,
          args := #[lakefile.toString, jsonFile.toString],
          cwd := some dir
        }
        if out.exitCode != 0 then
          throwErrorAt leanStr
            m!"When running '{exe} {lakefile} {jsonFile}', the exit code was {out.exitCode}\n" ++
            m!"Stderr:\n{out.stderr}\n\nStdout:\n{out.stdout}\n\n"
        logBuild s!"extract-lakefile (in {dir})" out (some leanStr.raw)
        let json ← IO.FS.readFile jsonFile
        let json ← IO.ofExcept <| Json.parse json
        let package ← IO.ofExcept <| json.getObjValAs? String "package"
        let modJson ← IO.ofExcept <| json.getObjVal? "module"
        let mod ← match SubVerso.Module.Module.fromJson? modJson with
          | .ok v => pure v
          | .error e =>
            throwError m!"Failed to deserialize highlighted Lean code. Error: {indentD e}"
        let hl := mod.items.foldl (init := .empty) fun hl v => hl ++ v.code
        pure (package, hl)

      -- Surface any warnings or informational messages reported during elaboration.
      let msgs := getMessages hl
      let hl := dropBlanks hl
      for (l, msg) in msgs do
        match msg.severity with
        | .info => logSilentInfoAt (← lineStx l) msg.toString
        | .warning => logSilentAt (← lineStx l) .warning msg.toString
        | .error => logErrorAt (← lineStx l) msg.toString

      discard <| expectString "elaborated configuration output" expectedStr package
        (useLine := (·.any (! Char.isWhitespace ·)))

      if opts.show then
        return #[← ``(Verso.Doc.Block.other (Verso.Genre.Manual.InlineLean.Block.lean $(quote hl)) #[])]
      else
        return #[← ``(Verso.Doc.Block.empty)]
where
  /-- Locate the `extract-lakefile` executable in the current Lake workspace. -/
  findExtractLakefile : DocElabM System.FilePath := do
    let out ← IO.Process.output {cmd := "lake", args := #["env", "which", "extract-lakefile"]}
    if out.exitCode != 0 then
      throwError
        m!"When running 'lake env which extract-lakefile', the exit code was {out.exitCode}\n" ++
        m!"Stderr:\n{out.stderr}\n\nStdout:\n{out.stdout}\n\n"
    let some exe := out.stdout.splitOn "\n" |>.head?
      | throwError "No executable path found for 'extract-lakefile'"
    IO.FS.realPath exe
