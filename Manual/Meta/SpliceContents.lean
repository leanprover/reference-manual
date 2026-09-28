/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module
public import Verso.Doc.Elab

public section

namespace Manual

open Verso ArgParse Doc Elab
open Lean Elab

structure SpliceContentsConfig where
  moduleName : Ident

meta def SpliceContentsConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m SpliceContentsConfig :=
  SpliceContentsConfig.mk <$> .positional `moduleName .ident

@[part_command Lean.Doc.Parser.Block.command]
meta def spliceContents : PartCommand
  | .command v => do
    unless v.name.getId == `spliceContents do Lean.Elab.throwUnsupportedSyntax
    let {moduleName} ← SpliceContentsConfig.parse.run (← parseArgs v.args)
    let moduleIdent ←
      mkIdentFrom moduleName <$>
      realizeGlobalConstNoOverloadWithInfo (mkIdentFrom moduleName (docName moduleName.getId))
    let modulePart ← `(($moduleIdent).toPart)
    let contentsAsBlock ← ``(Block.concat (Part.content $modulePart))
    PartElabM.addBlock contentsAsBlock
  | _ =>
    throwUnsupportedSyntax
