/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoManual

import Manual.Intro
import Manual.Elaboration
import Manual.Types
import Manual.Language
import Manual.Terms
import Manual.Tactics
import Manual.Simp
import Manual.BasicTypes
import Manual.NotationsMacros
import Manual.IO
import Manual.Monads

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "The Lean Language Reference" =>
%%%
tag := "lean-language-reference"
%%%


This is the _Lean Language Reference_, an in-progress reference work on Lean.
It is intended to be a comprehensive, precise description of Lean: a reference work in which Lean users can look up detailed information, rather than a tutorial intended for new users.
For other documentation, please refer to the [Lean documentation site](https://lean-lang.org/documentation/).

This reference manual is not yet complete, but there's enough information to provide value to users.
The top priority is to add the missing information as quickly as possible while staying up to date with Lean development.
As the rest of the text is written, regular snapshots will be released, tracking upstream changes.
This snapshot covers Lean version {versionString}[].

Our prioritization of content is based on our best understanding of our users' needs.
Please use the [issue tracker](https://github.com/leanprover/reference-manual/issues) to help us better understand what you need to know.
In particular, please create or upvote issues for topics that are important to you.
Your feedback is much appreciated!
Once sufficient content is available, we will begin saving snapshots for each release of Lean and making them conveniently available.

API reference documentation is included from the Lean standard library source code.
Due to technical limitations at the moment, the Lean terms and examples embedded in it do not render as nicely as we would like.
In the near future, we will be working on removing these limitations.
Additionally, we will be adding missing API reference documentation and revising and improving the existing API reference documentation.

**Release History**

: 2024-12-16

  This is the initial release of the reference manual.

{include Manual.Intro}

{include Manual.Elaboration}

{include Manual.Types}

{include Manual.Language}

{include Manual.Terms}

{include Manual.Monads}

{include 0 Manual.IO}

{include 0 Manual.Tactics}

{include 0 Manual.Simp}

{include 0 Manual.BasicTypes}

# Standard Library
%%%
tag := "standard-library"
%%%


:::planned 109
Overview of the standard library, including types from the prelude and those that require imports.
:::

{include 0 Manual.NotationsMacros}

# Output from Lean

:::planned 122
 * {deftech}[Unexpanders]
 * {deftech key:="delaborate"}[Delaboration]
 * {deftech}[Pretty printing]
 * Parenthesizers
:::

# Elan
%%%
tag := "elan"
%%%


::: planned 74

This section will describe Elan and how to use it:

 * `lean-toolchain` files
 * `+`-syntax for toolchain selection
 * Specific overrides
 * Using a local development build of Lean with Elan
:::

# Lake and Reservoir
%%%
tag := "build-tools-and-distribution"
%%%

## Lake
%%%
tag := "lake"
%%%


::: planned 75
 * Port and organize the information in the Lake README
 * Describe the underlying Lake-specific concepts of traces, artifacts, workspaces, and facets
:::

## Reservoir
%%%
tag := "reservoir"
%%%


::: planned 76
 * Concepts
 * Package and toolchain versions
 * Tags and builds
:::

# Index
%%%
number := false
file := some "the-index"
%%%

{theIndex}



::::::draft

:::progress
```namespace
List
Function
Functor Applicative Monad Pure Bind Seq SeqLeft SeqRight
MonadState MonadStateOf StateT StateM
MonadReader MonadReaderOf ReaderT ReaderM
MonadExcept MonadExceptOf ExceptT Except
MonadFunctor MonadFunctorT
MonadControl MonadControlT
MonadLift MonadLiftT
OptionT
StateRefT'
StateCpsT
ExceptCpsT
LawfulFunctor
LawfulApplicative
LawfulMonad
Id
ForM
ForIn
ForInStep
ForIn'
EStateM EStateM.Result EStateM.Backtrackable
String Char Nat Lean.Elab.Tactic Array Subarray IO IO.FS System System.FilePath IO.Process IO.FS.Stream ST IO.Error IO.FS.Stream.Buffer IO.FS.Handle
IO.Process.SpawnArgs IO.Process.Output IO.Process.Child IO.Process.StdioConfig IO.Process.Stdio IO.Ref ST.Ref IO.FS.Metadata IO.FS.DirEntry EIO BaseIO
IO.FileRight IO.FS.Stream Task Task.Priority Unit PUnit
Bool Decidable
System.Platform
PLift ULift Subtype Option List
USize
UInt8 UInt16 UInt32 UInt64
Int8 Int16 Int32 Int64
```

```exceptions
Bool.toLBool
Bool.«term_^^_»
```

```exceptions
Decidable.or_not_self
```

```exceptions
String.revFindAux String.extract.go₂ String.substrEq.loop String.casesOn
String.offsetOfPosAux String.extract.go₁ String.mapAux String.firstDiffPos.loop String.utf8SetAux String.revPosOfAux String.replace.loop
String.rec String.recOn String.posOfAux String.splitAux String.foldrAux
String.splitOnAux String.intercalate.go String.anyAux String.findAux
String.utf8GetAux? String.foldlAux String.utf8GetAux
String.utf8PrevAux String.noConfusionType String.noConfusion
String.utf8ByteSize.go String.validateUTF8.loop
String.crlfToLf.go
String.fromUTF8.loop
String.one_le_csize
```

```exceptions
String.sluggify
```

```exceptions
Nat.anyM.loop
Nat.nextPowerOfTwo.go
Nat.foldRevM.loop
Nat.foldM.loop
Nat.foldTR.loop
Nat.recAux
Nat.allTR.loop
Nat.allM.loop
Nat.anyTR.loop
Nat.anyM.loop
Nat.toSuperDigitsAux
Nat.casesAuxOn
Nat.forM.loop
Nat.repeatTR.loop
Nat.forRevM.loop
Nat.toSubDigitsAux
```

```exceptions
Nat.one_pos
Nat.not_lt_of_lt
Nat.sub_lt_self
Nat.lt_or_gt
Nat.pow_le_pow_left
Nat.not_lt_of_gt
Nat.le_or_le
Nat.le_or_ge
Nat.pred_lt'
Nat.pow_le_pow_right
Nat.lt_iff_le_and_not_ge
Nat.mul_pred_right
Nat.mul_pred_left
Nat.prod_dvd_and_dvd_of_dvd_prod
Nat.lt_iff_le_and_not_ge
Nat.mul_pred_right
```

```exceptions
Nat.binductionOn
Nat.le.rec
Nat.le.recOn
Nat.le.casesOn
Nat.le.below
Nat.le.below.step
Nat.le.below.rec
Nat.le.below.recOn
Nat.le.below.refl
Nat.le.below.casesOn
```

```exceptions
EStateM.dummySave
EStateM.dummyRestore
```

```exceptions
Array.get?_size
Array.forIn'.loop
Array.mapM.map
Array.findIdx?.loop
Array.get_extract_loop_lt
Array.foldrM_eq_foldrM_data
Array.get?_push
Array.appendList_data
Array.insertAt.loop
Array.reverse.loop
Array.foldrM_eq_reverse_foldlM_data
Array.isPrefixOfAux
Array.takeWhile.go
Array.isPrefixOfAux
Array.size_eq_length_data
Array.qpartition.loop
Array.insertionSort.swapLoop
Array.foldl_data_eq_bind
Array.foldl_toList_eq_bind
Array.foldrMUnsafe
Array.get_swap_left
Array.get_extract_loop_ge_aux
Array.data_swap
Array.get_extract_loop_lt_aux
Array.get?_swap
Array.get_swap'
Array.mapM_eq_mapM_data
Array.anyM.loop
Array.getElem_eq_data_getElem
Array.get_swap_right
Array.get_extract_loop_ge
Array.foldrM.fold
Array.foldlM.loop
Array.take.loop
Array.mapMUnsafe
Array.binSearchAux
Array.eq_push_pop_back_of_size_ne_zero
Array.get?_push_eq
Array.append_data
Array.indexOfAux
Array.reverse_toList
Array.ofFn.go
Array.get?_eq_data_get?
Array.filterMap_data
Array.empty_data
Array.foldrMUnsafe.fold
Array.toListImpl
Array.filter_data
Array.get_swap_of_ne
Array.get_append_right
Array.getElem?_eq_toList_getElem?
Array.foldl_eq_foldl_data
Array.sequenceMap.loop
Array.toList_eq
Array.findSomeRevM?.find
Array.data_range
Array.forIn'Unsafe.loop
Array.foldlM_eq_foldlM_data
Array.getElem_eq_toList_getElem
Array.getElem_mem_data
Array.get_extract
Array.extract.loop
Array.foldlMUnsafe.fold
Array.data_set
Array.forIn'Unsafe
Array.mapMUnsafe.map
Array.mapM'.go
Array.pop_data
Array.appendCore.loop
Array.get?_len_le
Array.back_push
Array.all_def
Array.get_push_lt
Array.foldl_data_eq_map
Array.get?_eq_toList_get?
Array.isEqvAux
Array.getElem?_mem
Array.getElem_fin_eq_toList_get
Array.getElem?_eq_data_get?
Array.foldr_eq_foldr_data
Array.data_length
Array.get_push
Array.push_data
Array.toArray_data
Array.get_append_left
Array.insertionSort.traverse
Array.getElem_fin_eq_data_get
Array.toListLitAux
Array.map_data
Array.get?_push_lt
Array.get_extract_aux
Array.foldlMUnsafe
Array.qsort.sort
Array.any_def
Array.anyMUnsafe
Array.data_toArray
Array.mem_data
Array.get_swap
Array.mapFinIdxM.map
Array.data_pop
Array.anyMUnsafe.any
Array.mkArray0
Array.mkArray1
Array.mkArray2
Array.mkArray3
Array.mkArray4
Array.mkArray5
Array.mkArray6
Array.mkArray7
Array.mkArray8
Array.mkEmpty
Array.get_push_eq
Array.appendCore
Array.modifyMUnsafe
Array.mapSepElems
Array.mapSepElemsM
Array.toArrayLit
Array.getSepElems
Array.zipWithAux
Array.casesOn
Array.rec
Array.recOn
Array.noConfusion
Array.noConfusionType
Array.tacticArray_get_dec
Array.back_eq_back?
Array.mkArray_data
Array.getLit
```

```exceptions
Array.qpartition
```

```exceptions
Subarray.forInUnsafe.loop
Subarray.as
Subarray.casesOn
Subarray.recOn
Subarray.rec
Subarray.noConfusion
Subarray.noConfusionType
Subarray.forInUnsafe
Subarray.findSomeRevM?.find
```

```exceptions
Lean.Elab.Tactic.evalUnfold.go
Lean.Elab.Tactic.dsimpLocation.go
Lean.Elab.Tactic.withCollectingNewGoalsFrom.go
Lean.Elab.Tactic.evalRunTac.unsafe_impl_1
Lean.Elab.Tactic.evalRunTac.unsafe_1
Lean.Elab.Tactic.evalTactic.handleEx
Lean.Elab.Tactic.simpLocation.go
Lean.Elab.Tactic.instToSnapshotTreeTacticParsedSnapshot.go
Lean.Elab.Tactic.dsimpLocation'.go
Lean.Elab.Tactic.withRWRulesSeq.go
Lean.Elab.Tactic.runTermElab.go
Lean.Elab.Tactic.getMainGoal.loop
Lean.Elab.Tactic.elabSimpArgs.isSimproc?
Lean.Elab.Tactic.elabSimpArgs.resolveSimpIdTheorem?
Lean.Elab.Tactic.tactic.dbg_cache
Lean.Elab.Tactic.tactic.simp.trace
Lean.Elab.Tactic.liftMetaTacticAux
```

```exceptions

Lean.Elab.Tactic.elabSetOption
Lean.Elab.Tactic.evalSeq1
Lean.Elab.Tactic.evalSimp
Lean.Elab.Tactic.evalSpecialize
Lean.Elab.Tactic.evalTacticAt
Lean.Elab.Tactic.evalSimpAll
Lean.Elab.Tactic.evalIntro.introStep
Lean.Elab.Tactic.evalDone
Lean.Elab.Tactic.evalRevert
Lean.Elab.Tactic.evalRight
Lean.Elab.Tactic.evalUnfold
Lean.Elab.Tactic.evalConstructor
Lean.Elab.Tactic.evalTacticCDot
Lean.Elab.Tactic.evalTraceMessage
Lean.Elab.Tactic.evalClear
Lean.Elab.Tactic.evalIntroMatch
Lean.Elab.Tactic.evalInduction
Lean.Elab.Tactic.evalApply
Lean.Elab.Tactic.evalUnknown
Lean.Elab.Tactic.evalRefl
Lean.Elab.Tactic.evalTactic.throwExs
Lean.Elab.Tactic.evalDSimp
Lean.Elab.Tactic.evalSepTactics.goEven
Lean.Elab.Tactic.evalAllGoals
Lean.Elab.Tactic.evalSplit
Lean.Elab.Tactic.evalInjection
Lean.Elab.Tactic.evalParen
Lean.Elab.Tactic.evalFocus
Lean.Elab.Tactic.evalLeft
Lean.Elab.Tactic.evalRotateRight
Lean.Elab.Tactic.evalWithReducible
Lean.Elab.Tactic.evalTactic.expandEval
Lean.Elab.Tactic.evalTraceState
Lean.Elab.Tactic.evalCase'
Lean.Elab.Tactic.evalSepTactics.goOdd
Lean.Elab.Tactic.evalWithReducibleAndInstances
Lean.Elab.Tactic.evalTacticSeqBracketed
Lean.Elab.Tactic.evalTactic.eval
Lean.Elab.Tactic.evalAlt
Lean.Elab.Tactic.evalGeneralize
Lean.Elab.Tactic.evalRewriteSeq
Lean.Elab.Tactic.evalSleep
Lean.Elab.Tactic.evalDSimpTrace
Lean.Elab.Tactic.evalReplace
Lean.Elab.Tactic.evalOpen
Lean.Elab.Tactic.evalAssumption
Lean.Elab.Tactic.evalSepTactics
Lean.Elab.Tactic.evalWithUnfoldingAll
Lean.Elab.Tactic.evalMatch
Lean.Elab.Tactic.evalRepeat1'
Lean.Elab.Tactic.evalFailIfSuccess
Lean.Elab.Tactic.evalRename
Lean.Elab.Tactic.evalFirst.loop
Lean.Elab.Tactic.evalSimpTrace
Lean.Elab.Tactic.evalFirst
Lean.Elab.Tactic.evalSubstVars
Lean.Elab.Tactic.evalRunTac
Lean.Elab.Tactic.evalSymmSaturate
Lean.Elab.Tactic.evalWithAnnotateState
Lean.Elab.Tactic.evalTacticAtRaw
Lean.Elab.Tactic.evalDbgTrace
Lean.Elab.Tactic.evalSubst
Lean.Elab.Tactic.evalNativeDecide
Lean.Elab.Tactic.evalCalc
Lean.Elab.Tactic.evalCase
Lean.Elab.Tactic.evalRepeat'
Lean.Elab.Tactic.evalRefine
Lean.Elab.Tactic.evalContradiction
Lean.Elab.Tactic.evalSymm
Lean.Elab.Tactic.evalInjections
Lean.Elab.Tactic.evalExact
Lean.Elab.Tactic.evalRotateLeft
Lean.Elab.Tactic.evalFail
Lean.Elab.Tactic.evalTactic
Lean.Elab.Tactic.evalSimpAllTrace
Lean.Elab.Tactic.evalRefine'
Lean.Elab.Tactic.evalChoice
Lean.Elab.Tactic.evalInduction.checkTargets
Lean.Elab.Tactic.evalIntro
Lean.Elab.Tactic.evalAnyGoals
Lean.Elab.Tactic.evalCases
Lean.Elab.Tactic.evalDelta
Lean.Elab.Tactic.evalDecide
Lean.Elab.Tactic.evalChoiceAux
Lean.Elab.Tactic.evalTacticSeq
Lean.Elab.Tactic.evalCheckpoint
Lean.Elab.Tactic.evalRenameInaccessibles
Lean.Elab.Tactic.evalIntros
Lean.Elab.Tactic.evalApplyLikeTactic
Lean.Elab.Tactic.evalSkip
Lean.Elab.Tactic.evalCalc.throwFailed
Lean.Elab.Tactic.evalSubstEqs
Lean.Elab.Tactic.evalTacticSeq1Indented
```

```exceptions
IO.stdGenRef
IO.throwServerError
IO.initializing
```

```exceptions
IO.Process.StdioConfig.noConfusionType
IO.Process.StdioConfig.recOn
IO.Process.StdioConfig.rec
IO.Process.StdioConfig.noConfusion
IO.Process.StdioConfig.casesOn
```

```exceptions
IO.FS.lines.read
```


```exceptions
IO.FS.Handle.readBinToEndInto.loop
```

```exceptions
IO.FS.Stream.readLspNotificationAs
IO.FS.Stream.readNotificationAs
IO.FS.Stream.readResponseAs
IO.FS.Stream.writeLspNotification
IO.FS.Stream.readJson
IO.FS.Stream.readLspMessage
IO.FS.Stream.Buffer.casesOn
IO.FS.Stream.Buffer.noConfusion
IO.FS.Stream.Buffer.recOn
IO.FS.Stream.Buffer.noConfusionType
IO.FS.Stream.Buffer.rec
IO.FS.Stream.rec
IO.FS.Stream.writeLspRequest
IO.FS.Stream.writeResponseError
IO.FS.Stream.noConfusionType
IO.FS.Stream.writeLspResponseErrorWithData
IO.FS.Stream.readLspResponseAs
IO.FS.Stream.noConfusion
IO.FS.Stream.writeLspResponse
IO.FS.Stream.readLspRequestAs
IO.FS.Stream.casesOn
IO.FS.Stream.readMessage
IO.FS.Stream.writeLspMessage
IO.FS.Stream.writeResponseErrorWithData
IO.FS.Stream.recOn
IO.FS.Stream.writeRequest
IO.FS.Stream.writeJson
IO.FS.Stream.writeLspResponseError
IO.FS.Stream.chainLeft
IO.FS.Stream.readRequestAs
IO.FS.Stream.withPrefix
IO.FS.Stream.writeResponse
IO.FS.Stream.chainRight
IO.FS.Stream.writeNotification
IO.FS.Stream.writeMessage
```
```exceptions
System.FilePath.recOn
System.FilePath.noConfusion
System.FilePath.casesOn
System.FilePath.walkDir.go
System.FilePath.rec
System.FilePath.noConfusionType
```

```exceptions
List.tacticSizeOf_list_dec
Lean.Parser.Tactic.tacticRefine_lift_
Lean.Parser.Tactic.tacticRefine_lift'_
Array.tacticArray_mem_dec
Lean.Parser.Tactic.normCast0
tacticClean_wf
Lean.Parser.Tactic.nestedTactic
Lean.Parser.Tactic.unknown
Lean.Parser.Tactic.paren
tacticDecreasing_trivial_pre_omega
```

```exceptions
IO.Process.Stdio.toCtorIdx
```

```exceptions
BaseIO.mapTasks.go
```
:::

::::::
