import VersoManual
import Manual.Meta.ErrorExplanation

open Lean
open Verso.Genre.Manual (logError)
set_option doc.verso true
variable [Monad m] [MonadError m]

structure ErrorExplanationExtendedMetadata extends ErrorExplanation.Metadata where
  name : Name
deriving ToJson, FromJson, Quote

block_extension Block.errorExplanationHeader (metadata : ErrorExplanationExtendedMetadata) where
  data := toJson metadata
  init st := st
    |>.setDomainTitle Manual.errorExplanationDomain "Error Explanations"
    |>.setDomainDescription Manual.errorExplanationDomain
        "Explanations of error messages and warnings produced during compilation"
    |>.addQuickJumpMapper Manual.errorExplanationDomain Manual.errorExplanationDomainMapper

  traverse id info _ := do
    let .ok errorMetadata := FromJson.fromJson? (α := ErrorExplanationExtendedMetadata) info
      | logError s!"Invalid JSON for error explanation:\n{info}"; pure none
    modify (·.saveDomainObject Manual.errorExplanationDomain errorMetadata.name.toString id)

    let tag ← Verso.Genre.Manual.externalTag id (← read).path errorMetadata.name.toString
    println! s!"Making tag for {tag}"
    pure none

  toTeX := none
  extraCss := ["
  .error-explanation-metadata {
    margin-bottom: 2rem; /* Double the paragraph margin */
  }

  .error-explanation-metadatum:not(:last-child):after {
    content: '|';
    margin: 0 10px;
  }
  .error-explanation-removed-warning {
    border: 1px solid var(--verso-warning-color);
    border-radius: 0.5rem;
    padding-left: var(--verso--box-padding);
    padding-right: var(--verso--box-padding);
  }
  "]
  toHtml := some fun _goI _goB _id info _contents =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
    let .ok metadata := FromJson.fromJson? (α := ErrorExplanationExtendedMetadata) info
      | HtmlT.logError "Failed to parse info for error explanation metadata block:\n{metadata}"
        pure .empty
    let deprecatedWarning :=
      if metadata.removedVersion?.isSome then
        {{ <div class="error-explanation-removed-warning">
             <p><strong>"Note: "</strong> "This diagnostic is no longer produced."</p>
           </div> }}
      else
        .empty
    let sevText := if metadata.severity matches .warning then "Warning" else "Error"
    let entries := #[("Severity", sevText), ("Since", metadata.sinceVersion)]
      ++ (metadata.removedVersion?.map fun v => #[("Removed", v)]).getD #[]
    let entries := entries.map fun (label, data) =>
      {{ <span class="error-explanation-metadatum">
           <strong>{{Html.text true label}}": "</strong>
           {{Html.text true data}}
          </span> }}
    return {{
      <div class="error-explanation-metadata">
        {{deprecatedWarning}}
        <p>"Error code: "<code>{{metadata.name.toString}}</code></p>
        <p><em>{{metadata.summary}}</em></p>
        <p>{{entries}}</p>
      </div>
    }}

structure ErrorHeaderConfig where
  name : Name
instance : Verso.ArgParse.FromArgs ErrorHeaderConfig m where
  fromArgs :=
    ErrorHeaderConfig.mk <$> Verso.ArgParse.positional `title Verso.ArgParse.ValDesc.name

/--
Error explanations start with header inserted by the {lit}`{errorExplanationHeader}` block command.

This elaboration of this command contains a {name}`Block.errorExplanationHeader` block that
handles both formatting the header and inserting the external reference to the error identifier.

Concretely, traversing the {name}`Block.errorExplanationHeader` block generated from the
command {lit}`{errorExplanationHeader lean.inductiveParamMissing}`
registers the error name {lean}`` `lean.unknownIdentifier`` with the domain {name}`Manual.errorExplanationDomain`
so that the URI

```
https://lean-lang.org/doc/reference/latest/find/?domain=Manual.errorExplanation&name=lean.unknownIdentifier
```

will redirect to a URI like

```
https://lean-lang.org/doc/reference/latest/Error-Explanations/lean___unknownIdentifier/#lean___unknownIdentifier
```
-/
@[block_command]
def errorExplanationHeader : Verso.Doc.Elab.BlockCommandOf ErrorHeaderConfig
  | cfg, _contents => do
    match ← getErrorExplanation? cfg.name with
    | .none =>
      let metadata := ErrorExplanationExtendedMetadata.mk (ErrorExplanation.Metadata.mk "Summary unavailable" "Metadata unavailable" MessageSeverity.error Option.none) cfg.name
      ``(Doc.Block.other (Block.errorExplanationHeader $(quote metadata)) #[])
    | .some explan =>
      let metadata := ErrorExplanationExtendedMetadata.mk explan.metadata cfg.name
      ``(Doc.Block.other (Block.errorExplanationHeader $(quote metadata)) #[])
