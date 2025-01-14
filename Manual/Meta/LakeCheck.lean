/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Elab.Command
import Lean.Elab.InfoTree

import Verso
import Verso.Doc.ArgParse
import Verso.Doc.Elab.Monad
import VersoManual
import Verso.Code

import SubVerso.Highlighting
import SubVerso.Examples

import Manual.Meta.Basic
import Manual.Meta.Lean.Scopes
import Manual.Meta.Lean.Block


open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets
open SubVerso.Highlighting Highlighted

open Lean.Elab.Tactic.GuardMsgs

namespace Manual

/--
Check that the output of `lake --help` has not changed unexpectedly
-/
@[code_block_expander lakeHelp]
def lakeHelp : CodeBlockExpander
  | args, str => do
    let () ← ArgParse.done.run args
    let out ← IO.Process.output {cmd := "lake", args := #["--help"]}
    if out.exitCode != 0 then
      throwError
        m!"When running 'lake --help', the exit code was {out.exitCode}\n" ++
        m!"Stderr:\n{out.stderr}\n\nStdout:\n{out.stdout}\n\n"
    let lakeOutput := out.stdout
    let expectedLines := str.getString.splitOn "\n" |>.filter useLine |>.toArray
    let actualLines := lakeOutput.splitOn "\n" |>.filter useLine |>.toArray


    unless expectedLines == actualLines do
      let diff := Diff.diff expectedLines actualLines
      logErrorAt str m!"Mismatching 'lake --help' output:\n{Diff.linesToString diff}"
      let lakeOutput := lakeOutput.dropWhile (· ≠ '\n') |>.dropWhile (· == '\n')
      Suggestion.saveSuggestion str ((lakeOutput.take 30) ++ "…") lakeOutput

    return #[]

where
  -- Ignore the version spec or empty lines to reduce false positives
  useLine (l : String) : Bool :=
    !l.isEmpty && !"Lake version ".isPrefixOf l
