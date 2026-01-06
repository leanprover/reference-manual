/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Verso
import Verso.Doc.ArgParse
import Verso.Doc.Elab.Monad
import VersoManual
import Verso.Code

namespace Manual

open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets
open Lean Elab
open Lean.Doc.Syntax

structure SpliceContentsConfig where
  moduleName : Ident

def SpliceContentsConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m SpliceContentsConfig :=
  SpliceContentsConfig.mk <$> .positional `moduleName .ident

@[part_command Lean.Doc.Syntax.command]
def spliceContents : PartCommand
  | `(block|command{spliceContents $args*}) => do
    let {moduleName} ← SpliceContentsConfig.parse.run (← parseArgs args)
    let moduleIdent ←
      mkIdentFrom moduleName <$>
      realizeGlobalConstNoOverloadWithInfo (mkIdentFrom moduleName (docName moduleName.getId))
    let modulePart ← `(($moduleIdent).toPart)
    let contentsAsBlock ← ``(Block.concat (Part.content $modulePart))
    PartElabM.addBlock contentsAsBlock
  | _ =>
    throwUnsupportedSyntax
