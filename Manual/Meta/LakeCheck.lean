/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
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
import Manual.Meta.ExpectString


open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets
open SubVerso.Highlighting Highlighted

open Lean.Elab.Tactic.GuardMsgs

namespace Manual

private partial def parseOpts [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m (List String) :=
  (many (.positional `subcommand stringOrIdent))
where
  many {α} (p : ArgParse m α) : ArgParse m (List α) :=
    (· :: ·) <$> p <*> many p <|> pure []

  stringOrIdent : ValDesc m String := {
    get
      | .name x => pure <| x.getId.toString (escape := false)
      | .str x => pure x.getString
      | .num n => throwErrorAt n "Expected string or identifier"

    description := "string or identifier"
  }


/--
Check that the output of `lake --help` has not changed unexpectedly
-/
@[code_block_expander lakeHelp]
def lakeHelp : CodeBlockExpander
  | args, str => do
    let sub ← parseOpts.run args
    let args := #["--help"] ++ sub.toArray
    let out ← IO.Process.output {cmd := "lake", args}
    if out.exitCode != 0 then
      throwError
        m!"When running 'lake --help', the exit code was {out.exitCode}\n" ++
        m!"Stderr:\n{out.stderr}\n\nStdout:\n{out.stdout}\n\n"
    let lakeOutput := out.stdout

    discard <| expectString "'lake --help' output" str lakeOutput (useLine := useLine)

    return #[]
where
  -- Ignore the version spec or empty lines to reduce false positives
  useLine (l : String) : Bool :=
    !l.isEmpty && !"Lake version ".isPrefixOf l
