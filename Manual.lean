/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoManual

import Manual.Intro
import Manual.Elaboration
import Manual.Types
import Manual.SourceFiles
import Manual.Attributes
import Manual.Defs
import Manual.Classes
import Manual.Axioms
import Manual.Terms
import Manual.ErrorExplanations
import Manual.Tactics
import Manual.Simp
import Manual.Grind
import Manual.VCGen
import Manual.BasicTypes
import Manual.BasicProps
import Manual.NotationsMacros
import Manual.IO
import Manual.Interaction
import Manual.Monads
import Manual.BuildTools
import Manual.Releases
import Manual.Namespaces
import Manual.Runtime
import Manual.SupportedPlatforms

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option maxRecDepth 1024

#doc (Manual) "The Lean Language Reference" =>
%%%
tag := "lean-language-reference"
shortContextTitle := "Lean Reference"
%%%

This is the _Lean Language Reference_.
It is intended to be a comprehensive, precise description of Lean: a reference work in which Lean users can look up detailed information, rather than a tutorial intended for new users.
For other documentation, please refer to the [Lean documentation overview](https://lean-lang.org/documentation/).
This manual covers Lean version {versionString}[].

Lean is an *interactive theorem prover* based on dependent type theory, designed for use both in cutting-edge mathematics and in software verification.
Lean's core type theory is expressive enough to capture very complicated mathematical objects, but simple enough to admit independent implementations, reducing the risk of bugs that affect soundness.
The core type theory is implemented in a minimal {tech}[kernel] that does nothing other than check proof terms.
This core theory and kernel are supported by advanced automation, realized in {ref "tactics"}[an expressive tactic language].
Each tactic produces a term in the core type theory that is checked by the kernel, so bugs in tactics do not threaten the soundness of Lean as a whole.
Along with many other parts of Lean, the tactic language is user-extensible, so it can be built up to meet the needs of a given formalization project.
Tactics are written in Lean itself, and can be used immediately upon definition; rebuilding the prover or loading external modules is not required.

Lean is also a pure *functional programming language*, with features such as a run-time system based on reference counting that can efficiently work with packed array structures, multi-threading, and monadic {name}`IO`.
As befits a programming language, Lean is primarily implemented in itself, including the language server, build tool, {tech}[elaborator], and tactic system.
This very book is written in [Verso](https://github.com/leanprover/verso), a documentation authoring tool written in Lean.

Familiarity with Lean's programming features is valuable even for users whose primary interest is in writing proofs, because Lean programs are used to implement new tactics and proof automation.
Thus, this reference manual does not draw a barrier between the two aspects, but rather describes them together so they can shed light on one another.



{include 0 Manual.Intro}

{include 0 Manual.Elaboration}

{include 0 Manual.Interaction}

{include 0 Manual.Types}

{include 0 Manual.SourceFiles}

{include 0 Manual.Namespaces}

{include 0 Manual.Defs}

{include 0 Manual.Axioms}

{include 0 Manual.Attributes}

{include 0 Manual.Terms}

{include 0 Manual.Classes}

{include 0 Manual.Coercions}

{include 0 Manual.Tactics}

{include 0 Manual.Monads}

{include 0 Manual.IO}

{include 0 Manual.Simp}

{include 0 Manual.Grind}

{include 0 Manual.VCGen}

{include 0 Manual.BasicProps}

{include 0 Manual.BasicTypes}

# Dynamic Typing
%%%
draft := true
%%%

{docstring TypeName}

{docstring Dynamic}

{docstring Dynamic.mk +allowMissing}

{docstring Dynamic.get?}


# Standard Library
%%%
tag := "standard-library"
draft := true
%%%


:::planned 109
Overview of the standard library, including types from the prelude and those that require imports.
:::

{include 0 Manual.NotationsMacros}


{include 0 Manual.Runtime}


{include 0 Manual.BuildTools}

{include 0 Manual.ErrorExplanations}

{include 0 Manual.Releases}

{include 0 Manual.SupportedPlatforms}

# Index
%%%
number := false
file := some "the-index"
%%%

{theIndex}

# Progress
%%%
number := false
draft := true
file := some "the-index"
%%%


::::::draft

:::progress
```namespace
ByteArray
ByteArray.Iterator
ByteSlice
List
Int
IntCast
Empty
PEmpty
Function
Ord
Ordering
Functor
Applicative
Monad
Pure
Bind
Seq
SeqLeft
SeqRight
MonadState
MonadStateOf
StateT
StateM
MonadReader
MonadReaderOf
ReaderT
ReaderM
MonadExcept
MonadExceptOf
ExceptT
Except
MonadFunctor
MonadFunctorT
MonadControl
MonadControlT
MonadLift
MonadLiftT
OptionT
StateRefT'
StateCpsT
ExceptCpsT
LawfulFunctor
LawfulApplicative
LawfulMonad
LawfulBEq
ReflBEq
EquivBEq
LawfulHashable
Id
Thunk
ForM
ForIn
ForInStep
ForIn'
EStateM
EStateM.Result
EStateM.Backtrackable
String
Substring
String.Slice
String.Slice.Pos
String.Pattern
String.Pos.Raw
String.Pos
String.ValidPos
String.Iterator
Char
Nat
Lean.Elab.Tactic
Array
Subarray
IO
IO.FS
System
System.FilePath
IO.Process
IO.FS.Stream
ST
IO.Error
IO.FS.Stream.Buffer
IO.FS.Handle
IO.Process.SpawnArgs
IO.Process.Output
IO.Process.Child
IO.Process.StdioConfig
IO.Process.Stdio
IO.Ref
ST.Ref
IO.FS.Metadata
IO.FS.DirEntry
EIO
BaseIO
IO.FileRight
IO.AccessRight
IO.FS.Stream
Task
Task.Priority
IO.Promise
Std.Mutex
Std.Channel
Std.Channel.Sync
Std.CloseableChannel
Std.Condvar
Std.Format
Unit
PUnit
Bool
Decidable
System.Platform
PLift
ULift
Subtype
Option
List
List.IsSuffix
List.IsPrefix
List.IsInfix
List.Perm
List.Pairwise
List.Nodup
List.Lex
USize
UInt8
UInt16
UInt32
UInt64
ISize
Int8
Int16
Int32
Int64
Fin
Option
List
Prod
PProd
MProd
Sum
PSum
Sigma
Subtype
Repr
Thunk
_root_
BitVec
Float
Float32
Empty
Quotient
Quot
Setoid
Squash
Subsingleton
WellFoundedRelation
Equivalence
HasEquiv
Lake
Lake.RecBuildM
Lake.FetchM
Lake.ScriptM
MonadEval
True
False
And
Or
Not
Iff
Exists
Eq
HEq
Max
Min
Std.HashMap
Std.ExtHashMap
Std.DHashMap
Std.ExtDHashMap
Std.HashSet
Std.ExtHashSet
Std.TreeMap
Std.DTreeMap
Std.TreeSet
```

```exceptions
Std.HashMap.all
Std.HashMap.equiv_emptyWithCapacity_iff_isEmpty.match_1_1
Std.HashMap.noConfusionType.withCtor
Std.HashMap.noConfusionType.withCtorType
Std.HashMap.«term_~m_»
```

```exceptions
Std.DHashMap.equiv_emptyWithCapacity_iff_isEmpty.match_1_1
Std.DHashMap.insertMany_ind.match_1_1
Std.DHashMap.isSetoid
Std.DHashMap.«term_~m_»
```

```exceptions
Std.ExtHashMap.noConfusionType.withCtor
Std.ExtHashMap.noConfusionType.withCtorType
```

```exceptions
Bool.toLBool
Bool.atLeastTwo
Bool.«term_^^_»
```

```exceptions
Decidable.or_not_self
```

```exceptions
Sum.repr
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
String.mangle
```
```exceptions
String.codepointPosToUtf16Pos
String.codepointPosToUtf16PosFrom
String.codepointPosToUtf8PosFrom
String.fromExpr?
String.reduceBinPred
String.reduceBoolPred
String.toFileMap
String.utf16Length
String.utf16PosToCodepointPos
String.utf16PosToCodepointPosFrom
```

```exceptions
Substring.commonPrefix.loop
Substring.commonSuffix.loop
Substring.splitOn.loop
Substring.takeRightWhileAux
Substring.takeWhileAux
```

```exceptions
String.Pos.Raw.ctorIdx
String.Pos.Raw.extract.go₁
String.Pos.Raw.extract.go₂
String.Pos.Raw.mk.noConfusion
String.Pos.Raw.utf8GetAux
String.Pos.Raw.utf8GetAux?
String.Pos.Raw.utf8PrevAux
String.Pos.Raw.utf8SetAux
```

```exceptions
String.Slice.ctorIdx
String.Slice.hash
String.Slice.instDecidableEqPos.decEq
String.Slice.instInhabitedByteIterator.default
String.Slice.instInhabitedPosIterator.default
String.Slice.instInhabitedRevPosIterator.default
String.Slice.instInhabitedRevSplitIterator.default
String.Slice.instInhabitedSplitInclusiveIterator.default
String.Slice.instInhabitedSplitIterator.default
String.Slice.lines.lineMap
String.Slice.mk.noConfusion
```

```exceptions
String.Slice.Pos.ctorIdx
String.Slice.Pos.mk.noConfusion
String.Slice.Pos.prevAux
String.Slice.Pos.prevAux.go
```

```exceptions
String.ValidPos.ctorIdx
String.ValidPos.mk.noConfusion
```

```exceptions
Char.ofNatAux
Char.quoteCore
Char.quoteCore.smallCharToHex
Char.notLTTrans
Char.notLTTotal
Char.notLTAntisymm
Char.repr
```

```exceptions
Char.fromExpr?
Char.reduceBinPred
Char.reduceBoolPred
Char.reduceUnary
```

```exceptions
BitVec.fromExpr?
BitVec.negOverflow
BitVec.reduceBin
BitVec.reduceBinPred
BitVec.reduceBoolPred
BitVec.reduceExtend
BitVec.reduceGetBit
BitVec.reduceShift
BitVec.reduceShiftShift
BitVec.reduceShiftWithBitVecLit
BitVec.reduceUnary
```

```exceptions
ByteArray.ctorIdx
ByteArray.findFinIdx?.loop
ByteArray.findIdx?.loop
ByteArray.foldlM.loop
ByteArray.foldlMUnsafe
ByteArray.foldlMUnsafe.fold
ByteArray.forIn.loop
ByteArray.forInUnsafe
ByteArray.forInUnsafe.loop
ByteArray.hash
ByteArray.instBEq.beq
ByteArray.instInhabitedIterator.default
ByteArray.mk.noConfusion
ByteArray.mkIterator
ByteArray.toList.loop
ByteArray.utf8Decode?.go
ByteArray.utf8DecodeChar?.assemble₁
ByteArray.utf8DecodeChar?.assemble₂
ByteArray.utf8DecodeChar?.assemble₂Unchecked
ByteArray.utf8DecodeChar?.assemble₃
ByteArray.utf8DecodeChar?.assemble₃Unchecked
ByteArray.utf8DecodeChar?.assemble₄
ByteArray.utf8DecodeChar?.assemble₄Unchecked
ByteArray.utf8DecodeChar?.isInvalidContinuationByte
ByteArray.utf8DecodeChar?.parseFirstByte
```

```exceptions
Quot.indep
Quot.lcInv
```

```exceptions
String.Pos.isValid.go
```

```exceptions
String.sluggify
```

```exceptions
Ordering.ofNat
Ordering.toCtorIdx
```

```exceptions
Ord.arrayOrd
```

```exceptions
Nat.applyEqLemma
Nat.applySimprocConst
Nat.div.go
Nat.fromExpr?
Nat.imax
Nat.lt_wfRel
Nat.modCore.go
Nat.reduceBin
Nat.reduceBinPred
Nat.reduceBoolPred
Nat.reduceLTLE
Nat.reduceNatEqExpr
Nat.reduceUnary
Nat.toDigitsCore
Nat.toLevel
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
BitVec.rotateLeftAux
BitVec.rotateRightAux
BitVec.unexpandBitVecOfNat
BitVec.unexpandBitVecOfNatLt
```

```exceptions
Id.hasBind
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
Array.zipWithAll.go
Array.shrink.loop
Array.idxOfAux
Array.firstM.go
Array.get!Internal
Array.getInternal
Array.findFinIdx?.loop
Array.insertIdx.loop
```

```exceptions
Array.qpartition
```

```exceptions
Option.toLOption
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
Int.add_of_le
Int.fromExpr?
Int.reduceBin
Int.reduceBinIntNatOp
Int.reduceBinPred
Int.reduceBoolPred
Int.reduceNatCore
Int.reduceUnary
```

```exceptions
Int8.fromExpr
Int16.fromExpr
Int32.fromExpr
Int64.fromExpr
ISize.fromExpr
UInt8.fromExpr
UInt16.fromExpr
UInt32.fromExpr
UInt64.fromExpr
USize.fromExpr
```

```exceptions
System.Platform.getIsEmscripten
System.Platform.getIsOSX
System.Platform.getIsWindows
System.Platform.getNumBits
System.Platform.getTarget
```

```exceptions
Prod.repr
Prod.rprod
Prod.lex
Prod.Lex
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
IO.Error.fopenErrorToString
IO.Error.mkAlreadyExists
IO.Error.mkAlreadyExistsFile
IO.Error.mkEofError
IO.Error.mkHardwareFault
IO.Error.mkIllegalOperation
IO.Error.mkInappropriateType
IO.Error.mkInappropriateTypeFile
IO.Error.mkInterrupted
IO.Error.mkInvalidArgument
IO.Error.mkInvalidArgumentFile
IO.Error.mkNoFileOrDirectory
IO.Error.mkNoSuchThing
IO.Error.mkNoSuchThingFile
IO.Error.mkOtherError
IO.Error.mkPermissionDenied
IO.Error.mkPermissionDeniedFile
IO.Error.mkProtocolError
IO.Error.mkResourceBusy
IO.Error.mkResourceExhausted
IO.Error.mkResourceExhaustedFile
IO.Error.mkResourceVanished
IO.Error.mkTimeExpired
IO.Error.mkUnsatisfiedConstraints
IO.Error.mkUnsupportedOperation
IO.Error.otherErrorToString
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
SubVerso.Compat.HashMap.Compat_simp_arith_all
Lean.Parser.Tactic.bvDecideMacro
Lean.Parser.Tactic.bvNormalizeMacro
Lean.Parser.Tactic.bvTraceMacro
Lean.Parser.Tactic.attemptAll
Lean.Parser.Tactic.tryResult
```



```exceptions
List.hasDecEq
List.zipIdxLE
List.toPArray'
List.maxNatAbs
List.minNatAbs
List.nonzeroMinimum
List.toAssocList'
List.toPArray'
List.countP.go
List.eraseDups.loop
List.eraseIdxTR.go
List.erasePTR.go
List.eraseReps.loop
List.eraseTR.go
List.filterAuxM
List.filterMapM.loop
List.filterMapTR.go
List.filterTR.loop
List.findFinIdx?.go
List.findIdx.go
List.findIdx?.go
List.flatMapM.loop
List.flatMapTR.go
List.forIn'.loop
List.insertIdxTR.go
List.intercalateTR.go
List.iotaTR.go
List.lengthTRAux
List.mapFinIdx.go
List.mapFinIdxM.go
List.mapIdx.go
List.mapIdxM.go
List.mapM.loop
List.mapTR.loop
List.modifyTR.go
List.partition.loop
List.partitionM.go
List.partitionMap.go
List.range'TR.go
List.range.loop
List.replaceTR.go
List.replicateTR.loop
List.reverseAux
List.setTR.go
List.span.loop
List.splitAt.go
List.splitBy.loop
List.takeTR.go
List.takeWhileTR.go
List.toArrayAux
List.toByteArray.loop
List.toFloatArray.loop
List.toPArray'.loop
List.toSMap
List.toSSet
List.zipWithTR.go
```

```exceptions
List.format
List.repr
List.repr'
List.«term_<+:_»
List.«term_<+_»
List.«term_<:+:_»
List.«term_<:+_»
List.«term_~_»
```

```exceptions
List.Perm.below
List.Lex.below
List.Pairwise.below
```

```exceptions
IO.Process.Stdio.toCtorIdx
```

```exceptions
BaseIO.mapTasks.go
```

```exceptions
Task.asServerTask
Task.mapList.go
```

```exceptions
Fin.foldrM.loop
Fin.induction.go
Fin.foldr.loop
Fin.foldlM.loop
Fin.foldl.loop
```

```exceptions
Fin.fromExpr?
Fin.reduceBin
Fin.reduceBinPred
Fin.reduceBoolPred
Fin.reduceNatOp
Fin.reduceOp
```

:::

::::::
