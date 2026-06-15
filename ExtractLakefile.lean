/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lake
import Lake.Load.Lean
import Lake.Load.Package

import SubVerso.Compat
import SubVerso.Highlighting.Code
import SubVerso.Module

import Manual.Meta.LakeToml.PackageTest

/-!
# Lean-format Lakefile Extractor

This executable elaborates a Lean-format `lakefile.lean` and emits, as JSON:

 * `package`: the elaborated `Lake.Package`, formatted with the same `Manual.Toml.Test` instances
   used to render the “expected elaboration result” for TOML lakefiles. This is the analog of what
   `checkTomlPackage` produces for a `lakefile.toml`, so that the `lakeLean` directive can validate
   it against an `expected` block exactly as `lakeToml` does.

 * `module`: the SubVerso highlighted representation of the lakefile source, so that the `lakeLean`
   directive can render the configuration with full syntax highlighting and hover information.

The implementation is based on `leanprover/verso-slides#21`: a Lean-format lakefile cannot be
elaborated by the ordinary module extractor, because it imports `Lake` and uses the package
configuration DSL (`package`, `lean_lib`, `lean_exe`, …). It must therefore be elaborated by a
process that statically links Lake's DSL, which is what this executable does.
-/

open SubVerso
open SubVerso.Highlighting (Highlighted highlightFrontendResult)
open SubVerso.Module (ModuleItem)

open Lean Elab System
open Lean.Elab.Command hiding Context
open Lean.Elab.Frontend

/-- Returns the node kind of the command, skipping outer `in` nodes. -/
partial def commandKind (cmd : Syntax) : SyntaxNodeKind :=
  match cmd with
  | `(command|$_cmd1 in $cmd2) => commandKind cmd2
  | _ => cmd.getKind

/--
Reconstruct a `Lake.Package` from the environment produced by elaborating a configuration file.
Mirrors `Lake.loadLeanConfig`, but operates on an already-elaborated environment so that the same
elaboration can also be highlighted.
-/
def extractPackage (env : Environment) (opts : Options := {}) : Lake.LogIO Lake.Package := do
  let fileCfg ← Lake.LakefileConfig.loadFromEnv env opts
  let .ok lakeEnv ← (Lake.Env.compute {home := ""} {sysroot := ""} none none).toBaseIO
    | Lake.error "Failed to compute a Lake environment"
  -- The recorded package directory and configuration file are canonical rather than the actual
  -- (temporary) location of the example, so that the elaboration result is deterministic.
  let loadCfg : Lake.LoadConfig := {
    lakeEnv, wsDir := ".", pkgDir := ".",
    relConfigFile := "lakefile.lean", configFile := "lakefile.lean"
  }
  return Lake.mkPackage loadCfg fileCfg

/--
Elaborate the configuration file at `configFile`, returning both the elaborated `Lake.Package`
and the SubVerso highlighting of its source.
-/
unsafe def extract (realConfigFile : FilePath) :
    IO (Lake.Package × SubVerso.Module.Module) := do
  initSearchPath (← findSysroot)

  -- The recorded package directory and configuration file are canonical rather than the actual
  -- (temporary) location of the example, so that the elaboration result is deterministic.
  let pkgDir : FilePath := "."
  let relConfigFile : FilePath := "lakefile.lean"

  let contents ← IO.FS.readFile realConfigFile
  let fm := FileMap.ofString contents
  let ictx := Parser.mkInputContext contents relConfigFile.toString
  let (headerStx, parserState, msgs) ← Parser.parseHeader ictx
  let imports := headerToImports headerStx

  -- Lake's DSL macros and attributes are registered via initializers, so they must run when the
  -- configuration's imports are loaded.
  enableInitializersExecution
  let env ← importModules imports {} (trustLevel := 1024) (loadExts := true)

  -- Configure the Lake DSL environment extensions exactly as `Lake.elabConfigFile` does, so that
  -- the package's name and directory defaults resolve the way Lake would resolve them.
  let env := env.setMainModule Lake.configModuleName
  let env := Lake.nameExt.setState env ⟨0, .anonymous⟩
  let env := Lake.dirExt.setState env (some pkgDir)
  let env := Lake.optsExt.setState env (some {})

  let pctx : Context := { inputCtx := ictx }
  let commandState : Command.State := { env, maxRecDepth := defaultMaxRecDepth, messages := msgs }
  -- `pp.tagAppFns` makes the highlighter associate constants with their applications.
  let scopes :=
    let sc := commandState.scopes[0]!
    { sc with opts := sc.opts.setBool `pp.tagAppFns true } :: commandState.scopes.tail!
  let commandState := { commandState with scopes }
  let cmdSt ← IO.mkRef { commandState, parserState, cmdPos := parserState.pos }

  let res ← Compat.Frontend.processCommands headerStx pctx cmdSt

  let finalState ← cmdSt.get
  let finalEnv := finalState.commandState.env
  if finalState.commandState.messages.hasErrors then
    let errs ← finalState.commandState.messages.toList.filterMapM fun m => do
      if m.severity == .error then pure (some (← m.toString)) else pure none
    throw <| .userError s!"{realConfigFile}: configuration has errors:\n{"\n".intercalate errs}"

  -- Extract the elaborated package configuration.
  let some pkg ← (extractPackage finalEnv).toBaseIO
    | throw <| .userError s!"{realConfigFile}: failed to load package configuration"

  -- Highlight the source.
  let res := res.updateLeading contents
  let hls ← (Frontend.runCommandElabM <| liftTermElabM <|
      highlightFrontendResult res (suppressNamespaces := [])) pctx cmdSt
  let items : Array ModuleItem := hls.zip res.syntax |>.map fun (hl, stx) => {
    defines := hl.definedNames.toArray
    kind := commandKind stx
    range := stx.getRange?.map fun ⟨s, e⟩ => (fm.toPosition s, fm.toPosition e)
    code := hl
  }

  return (pkg, SubVerso.Module.Module.mk items)

structure Args where
  lakefile : String
  jsonFile : String
  pkgDir? : Option String := none

def processArgs (args : List String) : IO Args := do
  let rec go (pkgDir? : Option String) (positional : Array String) :
      List String → IO Args
    | "--pkg-dir" :: dir :: more => go (some dir) positional more
    | arg :: more => go pkgDir? (positional.push arg) more
    | [] =>
      match positional.toList with
      | [lakefile, jsonFile] => pure { lakefile, jsonFile, pkgDir? }
      | other => throw <| .userError s!"\
          Expected: [--pkg-dir DIR] LAKEFILE OUT\n\
          where LAKEFILE is the path to a Lean-format lakefile and OUT is the destination of \
          the JSON.\n\
          Got positional arguments: {other}"
  go none #[] args

unsafe def main (args : List String) : IO UInt32 := do
  try
    let { lakefile, jsonFile, .. } ← processArgs args
    let (pkg, mod) ← extract lakefile
    let package := (Manual.Toml.Test.toString pkg).pretty ++ "\n"
    let out := Json.mkObj [
      ("package", Json.str package),
      ("module", mod.toJson)
    ]
    if let some parent := (jsonFile : FilePath).parent then
      IO.FS.createDirAll parent
    IO.FS.writeFile jsonFile (toString out)
    return (0 : UInt32)
  catch e =>
    IO.eprintln s!"extract-lakefile: {toString e}"
    return (1 : UInt32)
