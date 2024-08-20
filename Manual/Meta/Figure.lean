import VersoManual
import Lean.Elab.InfoTree.Types

open Verso Doc Elab
open Verso.Genre Manual
open Verso.ArgParse

open Lean Elab

namespace Verso.ArgParse

variable {m} [Monad m] [MonadInfoTree m] [MonadResolveName m] [MonadEnv m] [MonadError m] [MonadLiftT CoreM m] [MonadFileMap m]

def ValDesc.inlinesString : ValDesc m (Array Syntax) where
  description := m!"a string that contains a sequence of inline elements"
  get
    | .str s => open Lean.Parser in do
      let text ← getFileMap
      let input := s.getString
      let ictxt := mkInputContext input s!"string literal on line {s.raw.getPos?.map ((s!" on line {text.toPosition · |>.line}")) |>.getD ""}"
      let env ← getEnv
      let pmctx : ParserModuleContext := {env, options := {}}
      let p := Parser.textLine
      let s' := p.run ictxt pmctx (getTokenTable env) (mkParserState input)
      if s'.allErrors.isEmpty then
        if s'.stxStack.size = 1 then
          match s'.stxStack.back with
          | .node _ _ contents => pure contents
          | other => throwError "Unexpected syntax from Verso parser. Expected a node, got {other}"
        else throwError "Unexpected internal stack size from Verso parser. Expected 1, got {s'.stxStack.size}"
      else
        let mut msg := "Failed to parse:"
        for (p, _, e) in s'.allErrors do
          let {line, column} := text.toPosition p
          msg := msg ++ s!"  {line}:{column}: {toString e}\n    {repr <| input.extract p input.endPos}\n"
        throwError msg
    | other => throwError "Expected string, got {repr other}"


end Verso.ArgParse

namespace Manual

def Block.figure (name : Option String) : Block where
  name := `Manual.figure
  data := ToJson.toJson (name, (none : Option Tag))

structure FigureConfig where
  caption : Array Syntax
  /-- Name for refs -/
  name : Option String := none


def FigureConfig.parse [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] [MonadFileMap m] : ArgParse m FigureConfig :=
  FigureConfig.mk <$> .positional `caption .inlinesString <*> .named `name .string true

@[directive_expander figure]
def figure : DirectiveExpander
  | args, contents => do
    let cfg ← FigureConfig.parse.run args
    let caption ← cfg.caption.mapM elabInline
    let blocks ← contents.mapM elabBlock
    -- Figures are represented using the first block to hold the caption. Storing it in the JSON
    -- entails repeated (de)serialization.
    pure #[← ``(Block.other (Block.figure $(quote cfg.name)) #[Block.para #[$caption,*], $blocks,*])]

@[block_extension figure]
def figure.descr : BlockDescr where
  traverse id data contents := do
    match FromJson.fromJson? data (α := Option String × Option Tag) with
    | .error e => logError s!"Error deserializing figure tag: {e}"; pure none
    | .ok (none, _) => pure none
    | .ok (some x, none) =>
      let path ← (·.path) <$> read
      let tag ← Verso.Genre.Manual.externalTag id path x
      pure <| some <| Block.other {Block.figure none with id := some id, data := toJson (some x, some tag)} contents
    | .ok (some _, some _) => pure none
  toTeX :=
    some <| fun _ go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  toHtml :=
    open Verso.Doc.Html in
    open Verso.Output.Html in
    some <| fun goI goB id _data blocks => do
      if h : blocks.size < 1 then
        HtmlT.logError "Malformed figure"
        pure .empty
      else
        let .para caption := blocks[0]
          | HtmlT.logError "Malformed figure - caption not paragraph"; pure .empty
        let (_, _, xref) ← read
        let attrs := match xref.externalTags[id]? with
          | none => #[]
          | some (_, t) => #[("id", t)]
        pure {{
          <figure {{attrs}}>
            {{← blocks.extract 1 blocks.size |>.mapM goB}}
            <figcaption>{{← caption.mapM goI}}</figcaption>
          </figure>
        }}
