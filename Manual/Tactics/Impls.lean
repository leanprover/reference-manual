import VersoManual

import Lean.Parser.Term

import Manual.Meta


open Verso.Genre Manual

open Lean.Elab.Tactic

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "Tactic Implementations" =>

:::TODO
Delete this section, consider them implementation details
:::

These functions implement tactics.
Because they parse tactic syntax directly, they are not particularly convenient to call from {name}`TacticM` code.

{docstring Lean.Elab.Tactic.elabSetOption}

{docstring Lean.Elab.Tactic.evalSeq1}

{docstring Lean.Elab.Tactic.evalSimp}

{docstring Lean.Elab.Tactic.evalSpecialize}

{docstring Lean.Elab.Tactic.evalTacticAt}

{docstring Lean.Elab.Tactic.evalSimpAll}

{docstring Lean.Elab.Tactic.evalIntro.introStep}

{docstring Lean.Elab.Tactic.evalDone}

{docstring Lean.Elab.Tactic.evalRevert}

{docstring Lean.Elab.Tactic.evalRight}

{docstring Lean.Elab.Tactic.evalUnfold}

{docstring Lean.Elab.Tactic.evalConstructor}

{docstring Lean.Elab.Tactic.evalTacticCDot}

{docstring Lean.Elab.Tactic.evalTraceMessage}

{docstring Lean.Elab.Tactic.evalClear}

{docstring Lean.Elab.Tactic.evalIntroMatch}

{docstring Lean.Elab.Tactic.evalInduction}

{docstring Lean.Elab.Tactic.evalApply}

{docstring Lean.Elab.Tactic.evalUnknown}

{docstring Lean.Elab.Tactic.evalRefl}

{docstring Lean.Elab.Tactic.evalTactic.throwExs}

{docstring Lean.Elab.Tactic.evalDSimp}

{docstring Lean.Elab.Tactic.evalSepTactics.goEven}

{docstring Lean.Elab.Tactic.evalAllGoals}

{docstring Lean.Elab.Tactic.evalSplit}

{docstring Lean.Elab.Tactic.evalInjection}

{docstring Lean.Elab.Tactic.evalParen}

{docstring Lean.Elab.Tactic.evalFocus}

{docstring Lean.Elab.Tactic.evalLeft}

{docstring Lean.Elab.Tactic.evalRotateRight}

{docstring Lean.Elab.Tactic.evalWithReducible}

{docstring Lean.Elab.Tactic.evalTactic.expandEval}

{docstring Lean.Elab.Tactic.evalTraceState}

{docstring Lean.Elab.Tactic.evalCase'}

{docstring Lean.Elab.Tactic.evalSepTactics.goOdd}

{docstring Lean.Elab.Tactic.evalWithReducibleAndInstances}

{docstring Lean.Elab.Tactic.evalTacticSeqBracketed}

{docstring Lean.Elab.Tactic.evalTactic.eval}

{docstring Lean.Elab.Tactic.evalAlt}

{docstring Lean.Elab.Tactic.evalGeneralize}

{docstring Lean.Elab.Tactic.evalRewriteSeq}

{docstring Lean.Elab.Tactic.evalSleep}

{docstring Lean.Elab.Tactic.evalDSimpTrace}

{docstring Lean.Elab.Tactic.evalReplace}

{docstring Lean.Elab.Tactic.evalOpen}

{docstring Lean.Elab.Tactic.evalAssumption}

{docstring Lean.Elab.Tactic.evalSepTactics}

{docstring Lean.Elab.Tactic.evalWithUnfoldingAll}

{docstring Lean.Elab.Tactic.evalMatch}

{docstring Lean.Elab.Tactic.evalRepeat1'}

{docstring Lean.Elab.Tactic.evalFailIfSuccess}

{docstring Lean.Elab.Tactic.evalRename}

{docstring Lean.Elab.Tactic.evalFirst.loop}

{docstring Lean.Elab.Tactic.evalSimpTrace}

{docstring Lean.Elab.Tactic.evalFirst}

{docstring Lean.Elab.Tactic.evalSubstVars}

{docstring Lean.Elab.Tactic.evalRunTac}

{docstring Lean.Elab.Tactic.evalSymmSaturate}

{docstring Lean.Elab.Tactic.evalWithAnnotateState}

{docstring Lean.Elab.Tactic.evalTacticAtRaw}

{docstring Lean.Elab.Tactic.evalDbgTrace}

{docstring Lean.Elab.Tactic.evalSubst}

{docstring Lean.Elab.Tactic.evalNativeDecide}

{docstring Lean.Elab.Tactic.evalCalc}

{docstring Lean.Elab.Tactic.evalCase}

{docstring Lean.Elab.Tactic.evalRepeat'}

{docstring Lean.Elab.Tactic.evalRefine}

{docstring Lean.Elab.Tactic.evalContradiction}

{docstring Lean.Elab.Tactic.evalSymm}

{docstring Lean.Elab.Tactic.evalInjections}

{docstring Lean.Elab.Tactic.evalExact}

{docstring Lean.Elab.Tactic.evalRotateLeft}

{docstring Lean.Elab.Tactic.evalFail}

{docstring Lean.Elab.Tactic.evalTactic}

{docstring Lean.Elab.Tactic.evalSimpAllTrace}

{docstring Lean.Elab.Tactic.evalRefine'}

{docstring Lean.Elab.Tactic.evalChoice}

{docstring Lean.Elab.Tactic.evalInduction.checkTargets}

{docstring Lean.Elab.Tactic.evalIntro}

{docstring Lean.Elab.Tactic.evalAnyGoals}

{docstring Lean.Elab.Tactic.evalCases}

{docstring Lean.Elab.Tactic.evalDelta}

{docstring Lean.Elab.Tactic.evalDecide}

{docstring Lean.Elab.Tactic.evalChoiceAux}

{docstring Lean.Elab.Tactic.evalTacticSeq}

{docstring Lean.Elab.Tactic.evalCheckpoint}

{docstring Lean.Elab.Tactic.evalRenameInaccessibles}

{docstring Lean.Elab.Tactic.evalIntros}

{docstring Lean.Elab.Tactic.evalApplyLikeTactic}

{docstring Lean.Elab.Tactic.evalSkip}

{docstring Lean.Elab.Tactic.evalCalc.throwFailed}

{docstring Lean.Elab.Tactic.evalSubstEqs}

{docstring Lean.Elab.Tactic.evalTacticSeq1Indented}
