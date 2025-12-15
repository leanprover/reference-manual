import VersoManual

open Lean
open Verso.Genre.Manual

namespace Manual

def errorExplanationDomain := `Manual.errorExplanation

open Verso.Search in
def errorExplanationDomainMapper :=
  DomainMapper.withDefaultJs errorExplanationDomain "Error Explanation" "error-explanation-domain"
    |>.setFont { family := .code }

/-
inline_extension Inline.errorExplanation (errorName : Name) (summary : String) where
  data := ToJson.toJson #[errorName.toString, summary]

  traverse id info _ := do
    let .ok #[errorName, summary] := FromJson.fromJson? (α := Array String) info
      | logError s!"Invalid JSON for error explanation:\n{info}"; pure none
    modify fun s =>
      s |>.saveDomainObject errorExplanationDomain errorName id
        |>.saveDomainObjectData errorExplanationDomain errorName (json%{"summary": $summary})
    let path ← (·.path) <$> read
    discard <| Verso.Genre.Manual.externalTag id path errorName
    pure none

  toTeX := none
  toHtml := some fun go id _info contents =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
    let xref ← HtmlT.state
    let idAttr := xref.htmlId id
    return {{
      <span {{idAttr}}>
        {{← contents.mapM go}}
      </span>
    }}
-/
