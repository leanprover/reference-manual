import Lean

namespace Lean

structure ErrorExplanation.Metadata where
  summary : String
  sinceVersion : String
  severity : MessageSeverity     := .error
  removedVersion : Option String := none

structure ErrorExplanation where
  doc : String
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
  if name.isAnonymous then
    throwErrorAt nm "invalid name '{nm}'"
  validateDocComment docStx
  let doc ← getDocStringText docStx
  if errorExplanationExt.getState (← getEnv) |>.contains name then
    throwError m!"cannot add explanation: an error explanation for '{name}' already exists"
  modifyEnv (errorExplanationExt.addEntry · (name, { metadata, doc }))

def getErrorExplanation? [Monad m] [MonadEnv m] (name : Name) : m (Option ErrorExplanation) :=
  return errorExplanationExt.getState (← getEnv) |>.find? name

end Lean
