import Lean

namespace Lean

structure ErrorExplanation.Metadata where
  summary : String
  sinceVersion : String
  severity : MessageSeverity     := .error
  removedVersion : Option String := none
deriving FromJson, ToJson

structure ErrorExplanation.CodeBlockSet where
  broken : String
  brokenOutputs : Array String
  fixedWithOutputs : Array (String × Array String)
  deriving Repr

structure ErrorExplanation where
  doc : String
  codeBlocks : Array ErrorExplanation.CodeBlockSet
  metadata : ErrorExplanation.Metadata

-- FIXME: `addImportedFn`
initialize errorExplanationExt : SimplePersistentEnvExtension (Name × ErrorExplanation) (NameMap ErrorExplanation) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s (n, v) => s.insert n v
    addImportedFn := fun entries => RBMap.ofList entries.flatten.toList
  }
open Elab Meta Term Command in

/--
Registers an error explanation.

Note that the provided name is not relativized to the current namespace.
-/
elab docStx:docComment cmd:"register_error_explanation " nm:ident t:term : command => withRef cmd do
  let tp := mkConst ``ErrorExplanation.Metadata []
  let metadata ← runTermElabM <| fun _ => unsafe do
    let e ← elabTerm t tp
    if e.hasSyntheticSorry then throwAbortTerm
    evalExpr ErrorExplanation.Metadata tp e
  let name := nm.getId
  if name.isAnonymous then throwErrorAt nm "Invalid name for error explanation: '{nm}'"
  validateDocComment docStx
  let doc ← getDocStringText docStx
  if errorExplanationExt.getState (← getEnv) |>.contains name then
    throwError m!"Cannot add explanation: An error explanation already exists for '{name}'"
  modifyEnv (errorExplanationExt.addEntry · (name, { metadata, doc, codeBlocks := #[] }))

/--
Gets an error explanation for the given name if one exists, rewriting manual links.
-/
def getErrorExplanation? [Monad m] [MonadEnv m] [MonadLiftT BaseIO m] (name : Name) : m (Option ErrorExplanation) :=
  do
  let explan? := errorExplanationExt.getState (← getEnv) |>.find? name
  explan?.mapM fun explan =>
    return { explan with doc := (← rewriteManualLinks explan.doc) }

private partial def compareNamedExplanations (ne ne' : Name × ErrorExplanation) : Ordering :=
  match ne.2.metadata.removedVersion, ne'.2.metadata.removedVersion with
  | .none, .none | .some _, .some _ => compare ne.1.toString ne'.1.toString
  | .none, .some _ => .lt
  | .some _, .none => .gt

/--
Returns all error explanations with their names as a sorted array, rewriting manual links.
-/
def getErrorExplanationsSorted [Monad m] [MonadEnv m] [MonadLiftT BaseIO m] : m (Array (Name × ErrorExplanation)) := do
  let entries := errorExplanationExt.getState (← getEnv) |>.toArray
  entries
    |>.qsort (fun e e' => (compareNamedExplanations e e').isLT)
    |>.mapM fun (n, e) => return (n, { e with doc := (← rewriteManualLinks e.doc) })

def getErrorExplanationsRaw (env : Environment) : Array (Name × ErrorExplanation) :=
  errorExplanationExt.getState env |>.toArray

end Lean
