import Lean.Elab.Command
import Lean.Environment

open Lean Elab Command


namespace Manual.Meta.Lean.Scopes


initialize leanSampleScopes : Lean.EnvExtension (List Scope) ←
  Lean.registerEnvExtension (pure [])

def initScopes [Monad m] [MonadEnv m] [MonadOptions m] [MonadResolveName m] : m Unit := do
  if leanSampleScopes.getState (← getEnv) |>.isEmpty then
    let basicSc : Scope := {
        header :=  "",
        opts := ← getOptions,
        currNamespace := ← getCurrNamespace,
        openDecls := ← getOpenDecls
      }
    modifyEnv (leanSampleScopes.setState · [basicSc])

def getScopes [Monad m] [MonadEnv m] [MonadOptions m] [MonadResolveName m] : m (List Scope) := do
  initScopes
  return leanSampleScopes.getState (← getEnv)

def setScopes [Monad m] [MonadEnv m] (scopes : List Scope) : m Unit := do
  modifyEnv (leanSampleScopes.setState · scopes)

/--
A version of Lean.Elab.Command.runTermElabM that uses the saved scopes instead of the command
context to provide access to variables.
-/
def runWithVariables (elabFn : Array Expr → TermElabM α) : TermElabM α := do
  let scope := (← getScopes).head!
  Term.withAutoBoundImplicit <|
    Term.elabBinders scope.varDecls fun xs => do
      -- We need to synthesize postponed terms because this is a checkpoint for the auto-bound implicit feature
      -- If we don't use this checkpoint here, then auto-bound implicits in the postponed terms will not be handled correctly.
      Term.synthesizeSyntheticMVarsNoPostponing
      let mut sectionFVars := {}
      for uid in scope.varUIds, x in xs do
        sectionFVars := sectionFVars.insert uid x
      withReader ({ · with sectionFVars := sectionFVars }) do
        -- We don't want to store messages produced when elaborating `(getVarDecls s)` because they have already been saved when we elaborated the `variable`(s) command.
        -- So, we use `Core.resetMessageLog`.
        Core.resetMessageLog
        let someType := mkSort levelZero
        Term.addAutoBoundImplicits' xs someType fun xs _ =>
          Term.withoutAutoBoundImplicit <| elabFn xs
