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

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual Html Code Highlighted.WebAssets Syntax


structure SpliceContentsConfig where
  moduleName : Ident

def SpliceContentsConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : ArgParse m SpliceContentsConfig :=
  SpliceContentsConfig.mk <$> .positional `moduleName .ident

@[part_command Verso.Syntax.block_role]
def spliceContents : PartCommand
  | `(block|block_role{spliceContents $_args* }[ $content ]) => throwErrorAt content "Unexpected block argument"
  | `(block|block_role{spliceContents $args*}) => do
    let {moduleName} ← SpliceContentsConfig.parse.run (← parseArgs args)
    let moduleIdent ←
      mkIdentFrom moduleName <$>
      realizeGlobalConstNoOverloadWithInfo (mkIdentFrom moduleName (docName moduleName.getId))
    let contentsAsBlock ← ``(Block.concat (Part.content $moduleIdent))
    PartElabM.addBlock contentsAsBlock
  | _ =>
    throwUnsupportedSyntax
