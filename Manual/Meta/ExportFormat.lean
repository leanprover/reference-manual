/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module
public import Manual.Meta.LexedText.Basic
public meta import Manual.Meta.LexedText.Basic
public meta import Verso.Doc.Elab.Monad
public meta import Verso.Doc.Elab.Inline
public import VersoManual.Basic
import Verso.Doc.Elab.Monad
import VersoManual.Index
meta import Verso.Parser
public meta import Verso.Parser

public section

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual

namespace Manual

open Lean.Parser in
open Verso.Parser in
open LexedText in
/--
Highlights the JSON-like notation that describes the shape of objects in Lean's export format.

Quoted strings that precede a colon are field names, and other quoted strings are literal values.
Unquoted words such as `integer` or `RecursorVal` are types.
-/
private meta def exportFormatHl : Highlighter where
  name := "export-format"
  lexer :=
    token `brace (chFn '{' <|> chFn '}') <|>
    token `arr (chFn '[' <|> chFn ']') <|>
    token `angle (chFn '<' <|> chFn '>') <|>
    token `alt (chFn '|') <|>
    token `delim (chFn ',' <|> chFn ':') <|>
    token `key (atomicFn (str >> lookaheadFn (manyFn (chFn ' ') >> chFn ':'))) <|>
    token `lit str <|>
    token `type (satisfyFn Char.isAlpha >> manyFn (satisfyFn isWordChar))
  tokenClass := fun s => some (toString s.getKind)
where
  str := chFn '"' >> manyFn (satisfyEscFn (· != '"')) >> chFn '"'
  isWordChar (c : Char) : Bool := c.isAlphanum || c == '_'

private def exportFormat.css := "
.export-format {
  font-family: var(--verso-code-font-family);
}

figure.export-format {
  margin: 1rem 0;
}

figure.export-format > figcaption {
  font-family: var(--verso-structure-font-family);
  font-weight: 600;
  margin: 0 .75rem;
  text-align: left;
}

pre.export-format {
  margin: 0.25rem .75rem 0.5rem;
  padding: 0.1rem 0;
}

.export-format .key {
  color: #601020;
}

.export-format .lit {
  color: #107040;
}


.export-format {
  --export-format-type-color: #3030c0;
}

.export-format .type {
  color: var(--export-format-type-color);
  font-weight: 600;
}

/* Linked type names look exactly like unlinked ones, apart from the underline, in every link state. */
.export-format .type a,
.export-format .type a:link,
.export-format .type a:visited,
.export-format .type a:active,
.export-format .type a:focus {
  color: var(--export-format-type-color);
  font: inherit;
  text-decoration-line: underline;
  text-decoration-style: dotted;
  text-decoration-color: var(--export-format-type-color);
}

.export-format .type a:hover {
  text-decoration-style: solid;
}

.export-format .alt, .export-format .angle {
  font-weight: 600;
}
"

/-- The domain of export format types, each of which is named by the caption of its description. -/
def exportTypeDomain := `Manual.exportType

open Verso.Search in
private def exportTypeDomainMapper : DomainMapper :=
  DomainMapper.withDefaultJs exportTypeDomain "Export Format Type" "export-type-domain"

/-- Finds the link to the description of the export format type `name`, if there is one. -/
def exportTypeLink? (state : TraverseState) (name : String) : Option String := do
  let obj ← state.getDomainObject? exportTypeDomain name
  let id ← obj.ids.toList.head?
  return (← state.externalTags[id]?).link

/--
Registers the element with ID `id` as the description of the export format type `name`.

It reports an error if another element already describes the type.
-/
private def registerExportType (id : InternalId) (name : String) :
    ReaderT TraverseContext (StateT TraverseState (BuildLogT IO)) Unit := do
  if let some obj := (← get).getDomainObject? exportTypeDomain name then
    -- Only the first registration of this ID checks for duplicates, to avoid an error on every
    -- traversal pass.
    unless obj.ids.contains id do
      let others := obj.ids.toList.filterMap ((← get).externalTags[·]?) |>.map (·.link)
      reportError s!"Export format type '{name}' is described more than once; it is already described at {", ".intercalate others}"
  let path ← (·.path) <$> read
  let _ ← Verso.Genre.Manual.externalTag id path name
  Index.addEntry id {term := Verso.Doc.Inline.concat #[.text name, .text " (export format)"]}
  modify (·.saveDomainObject exportTypeDomain name id)

open Verso.Output Html in
/--
Converts highlighted export format text to HTML, linking each type name that has a description.
-/
private def exportFormatHtml (state : TraverseState) (text : LexedText) : Html :=
  text.content.map fun
    | (none, txt) => (txt : Html)
    | (some "type", txt) =>
      if let some url := exportTypeLink? state txt then
        {{<span class="type"><a href={{url}}>{{txt}}</a></span>}}
      else {{<span class="type">{{txt}}</span>}}
    | (some cls, txt) => {{<span class={{cls}}>{{txt}}</span>}}

block_extension Block.exportFormat (caption : String) (value : LexedText) where
  data := toJson (caption, value)
  init s :=
    s |>.setDomainTitle exportTypeDomain "Export Format Types"
      |>.addQuickJumpMapper exportTypeDomain exportTypeDomainMapper
  traverse id info _ := do
    let .ok ((caption, _) : String × LexedText) := fromJson? info
      | reportError s!"Failed to deserialize {info} as a captioned export format description"; return none
    registerExportType id caption
    return none
  toTeX := none
  extraCss := [exportFormat.css]
  toHtml := some <| fun _ _ id info _ => open Verso.Output.Html Verso.Doc.Html in do
    let .ok ((caption, v) : String × LexedText) := fromJson? info
      | reportError s!"Failed to deserialize {info} as a captioned export format description"; pure .empty
    let state ← HtmlT.state
    pure {{
      <figure class="export-format" {{state.htmlId id}}>
        <figcaption>{{caption}}</figcaption>
        <pre class="export-format">{{exportFormatHtml state v}}</pre>
      </figure>
    }}
  localContentItem _ info _ := open Verso.Output.Html in do
    let .ok ((caption, _) : String × LexedText) := fromJson? info
      | throw s!"Expected a caption and highlighted text, got {info}"
    let withSuffix := s!"{caption} (Export Format)"
    pure #[(caption, (caption : Html)), (withSuffix, (withSuffix : Html))]

structure ExportFormatConfig where
  caption : String

meta instance [Monad m] [MonadError m] : FromArgs ExportFormatConfig m where
  fromArgs := ExportFormatConfig.mk <$> .positional `caption .string

/--
Displays a captioned description of the shape of an object in Lean's export format, with syntax
highlighting.

The caption is a mandatory positional string argument.
-/
@[code_block]
meta def exportFormat : CodeBlockExpanderOf ExportFormatConfig
  | { caption }, str => do
    let codeStr := str.getVersoCodeBlock
    let toks ← LexedText.highlight exportFormatHl codeStr
    ``(Verso.Doc.Block.other (Block.exportFormat $(quote caption) $(quote toks)) #[Verso.Doc.Block.code $(quote codeStr)])

inline_extension Inline.exportType (name : String) (isDef : Bool) where
  data := toJson (name, isDef)
  traverse id data _ := do
    let .ok ((name, isDef) : String × Bool) := fromJson? data
      | reportError s!"Failed to deserialize {data} as an export format type name"; return none
    if isDef then registerExportType id name
    return none
  toTeX := none
  extraCss := [
r#"
a.export-type {
  color: inherit;
  text-decoration: currentcolor underline dotted;
}
a.export-type:hover {
  text-decoration: currentcolor underline solid;
}
"#
  ]
  toHtml := some <| fun goI id data contents => open Verso.Output.Html Verso.Doc.Html in do
    let .ok ((name, isDef) : String × Bool) := fromJson? data
      | reportError s!"Failed to deserialize {data} as an export format type name"; contents.mapM goI
    let state ← HtmlT.state
    -- A type named by a code literal is styled like the type names in `exportFormat` blocks, while
    -- custom link text is styled like the surrounding prose.
    let isTypeName := contents matches #[.code _]
    let typeName (body : Html) : Html := {{<code class="export-format"><span class="type">{{body}}</span></code>}}
    if isDef then
      if isTypeName then
        return {{<span class="export-type" {{state.htmlId id}}>{{typeName name}}</span>}}
      return {{<span class="export-type" {{state.htmlId id}}>{{← contents.mapM goI}}</span>}}
    let some url := exportTypeLink? state name
      | reportError s!"Unknown export format type '{name}'"; contents.mapM goI
    if isTypeName then
      return typeName {{<a href={{url}}>{{name}}</a>}}
    pure {{<a class="export-type" href={{url}}>{{← contents.mapM goI}}</a>}}
  localContentItem _ data _ := open Verso.Output.Html in do
    let .ok ((name, isDef) : String × Bool) := fromJson? data
      | throw s!"Expected an export format type name and a Boolean, got {data}"
    if isDef then
      let withSuffix := s!"{name} (Export Format)"
      pure #[(name, {{<code>{{name}}</code>}}), (withSuffix, {{<code>{{name}}</code>" (Export Format)"}})]
    else pure #[]

structure ExportTypeConfig where
  name? : Option String
  isDef : Bool

meta instance [Monad m] [MonadError m] : FromArgs ExportTypeConfig m where
  fromArgs :=
    ExportTypeConfig.mk <$> ((some <$> .positional `name .string) <|> pure none)
      <*> .flag `def false "If true, this is the definition site (i.e. the link target) for the type"

/--
Links to the description of an export format type.

The type is named either by a code literal, as in `{exportType}`Name.str``, or by a positional
argument that precedes the link text, as in `{exportType "Axiom"}[axioms]`. The `+def` flag marks
the definition site of a type that has no `exportFormat` block, as in `{exportType +def}`NameIdx``.
-/
@[role]
meta def exportType : RoleExpanderOf ExportTypeConfig
  | { name? := some name, isDef }, inlines => do
    let contents ← inlines.mapM elabInline
    ``(Verso.Doc.Inline.other (Inline.exportType $(quote name) $(quote isDef)) #[$contents,*])
  | { name? := none, isDef }, inlines => do
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let some { content := code, .. } := Lean.Doc.CodeView.of arg
      | throwErrorAt arg "Expected a code literal that names an export format type"
    let name := code.getVersoCode
    ``(Verso.Doc.Inline.other (Inline.exportType $(quote name) $(quote isDef)) #[Verso.Doc.Inline.code $(quote name)])

inline_extension Inline.exportField (name : String) where
  data := toJson name
  traverse _ _ _ := pure none
  toTeX := none
  extraCss := [exportFormat.css]
  toHtml := some <| fun goI _ data contents => open Verso.Output.Html in do
    let .ok (name : String) := fromJson? data
      | reportError s!"Failed to deserialize {data} as an export format field name"; contents.mapM goI
    pure {{<code class="export-format"><span class="key">s!"\"{name}\""</span></code>}}

/--
Displays the name of a field in an export format object, in the style of field names in
`exportFormat` blocks.

The name is written without quotes, as in `{exportField}`ie``, and it is displayed with quotes.
-/
@[role]
meta def exportField : RoleExpanderOf Unit
  | (), inlines => do
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let some { content := code, .. } := Lean.Doc.CodeView.of arg
      | throwErrorAt arg "Expected a code literal that names an export format field"
    let name := code.getVersoCode
    ``(Verso.Doc.Inline.other (Inline.exportField $(quote name)) #[Verso.Doc.Inline.code $(quote s!"\"{name}\"")])
