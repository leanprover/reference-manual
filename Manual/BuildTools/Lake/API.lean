/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Lean.Parser.Command
import Lake.Build.Package
import Lake.Build.Library
import Lake.Build.Module

import Manual.Meta

open Manual
open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option guard_msgs.diff true

open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "Script API Reference" =>
%%%
tag := "lake-api"
%%%

In addition to ordinary {lean}`IO` effects, Lake scripts have access to the Lake environment (which provides information about the current toolchain, such as the location of the Lean compiler) and the current workspace.
This access is provided in {name Lake.ScriptM}`ScriptM`.

{docstring Lake.ScriptM}

# Accessing the Environment

Monads that provide access to information about the current Lake environment (such as the locations of Lean, Lake, and other tools) have {name Lake.MonadLakeEnv}`MonadLakeEnv` instances.
This is true for all of the monads in the Lake API, including {name Lake.ScriptM}`ScriptM`.

{docstring Lake.MonadLakeEnv}

{docstring Lake.getLakeEnv}

{docstring Lake.getNoCache}

{docstring Lake.getTryCache}

{docstring Lake.getPkgUrlMap}

{docstring Lake.getElanToolchain}

## Search Path Helpers

{docstring Lake.getEnvLeanPath}

{docstring Lake.getEnvLeanSrcPath}

{docstring Lake.getEnvSharedLibPath}

## Elan Install Helpers

{docstring Lake.getElanInstall?}

{docstring Lake.getElanHome?}

{docstring Lake.getElan?}

## Lean Install Helpers

{docstring Lake.getLeanInstall}

{docstring Lake.getLeanSysroot}

{docstring Lake.getLeanSrcDir}

{docstring Lake.getLeanLibDir}

{docstring Lake.getLeanIncludeDir}

{docstring Lake.getLeanSystemLibDir}

{docstring Lake.getLean}

{docstring Lake.getLeanc}

{docstring Lake.getLeanSharedLib}

{docstring Lake.getLeanAr}

{docstring Lake.getLeanCc}

{docstring Lake.getLeanCc?}

## Lake Install Helpers

{docstring Lake.getLakeInstall}

{docstring Lake.getLakeHome}

{docstring Lake.getLakeSrcDir}

{docstring Lake.getLakeLibDir}

{docstring Lake.getLake}

# Accessing the Workspace

Monads that provide access to information about the current Lake workspace have {name Lake.MonadWorkspace}`MonadWorkspace` instances.
In particular, there are instances for {name Lake.ScriptM}`ScriptM` and {name Lake.LakeM}`LakeM`.

```lean -show
section
open Lake
#synth MonadWorkspace ScriptM

end
```

{docstring Lake.MonadWorkspace}

{docstring Lake.getRootPackage}

{docstring Lake.findPackageByName?}

{docstring Lake.findPackageByKey?}

{docstring Lake.findModule?}

{docstring Lake.findLeanExe?}

{docstring Lake.findLeanLib?}

{docstring Lake.findExternLib?}

{docstring Lake.getLeanPath}

{docstring Lake.getLeanSrcPath}

{docstring Lake.getSharedLibPath}

{docstring Lake.getAugmentedLeanPath}

{docstring Lake.getAugmentedLeanSrcPath }

{docstring Lake.getAugmentedSharedLibPath}

{docstring Lake.getAugmentedEnv}
