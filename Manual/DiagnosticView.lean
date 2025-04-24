/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Rotella
-/

import VersoManual

import Verso.Doc
import Verso.Syntax
import MD4Lean
import Manual.Meta
import Std.Internal.Parsec.String

import Manual.ErrorExplanation
import Manual.ErrorExplanationDummyData

open Verso.Genre.Manual.InlineLean

open Verso.Genre Manual

set_option pp.rawOnError true
set_option guard_msgs.diff true

/--
Converts an optional monadic computation into a monadic computation of an optional value.

This function only requires `m` to be an applicative functor.

Example:
```lean example
#eval show IO (Option String) from
  Option.sequence <| some do
    IO.println "hello"
    return "world"
```
```output
hello
```
```output
some "world"
```

Two Lean blocks:

```lean example
def x := 37
def y := 38
#eval x + y
```

```lean example
def y := ()
def x := ()
#eval some x <|> some y
```

Testing lang detection:

```lean notanexample
def x : String := "hello"
```

```notoutput
"hello"
```

This isn't even Lean:

```json
{ "the quick brown fox": "jumps over the lazy dog" }
```
-/
def badExDocstring := ()
def badExDocstring2 := ()

open Std.Internal Lean Elab Term Verso Doc Elab Genre Manual Markdown MD4Lean

section MyImpl

inductive ErrorExplanationCodeInfo.Kind
  | broken | fixed
deriving Repr, Inhabited, BEq

instance : ToString ErrorExplanationCodeInfo.Kind where
  toString
  | .broken => "broken"
  | .fixed => "fixed"

structure ErrorExplanationCodeInfo where
  lang : String
  kind? : Option ErrorExplanationCodeInfo.Kind
  name? : Option String
deriving Repr

namespace ErrorExplanationCodeInfo
open Parsec Parsec.String

namespace Parse

def word : Parser String := fun it =>
  -- TODO: be less restrictive about valid names
  let it' := it.find fun c => !c.isAlphanum
  .success it' (it.extract it')

def languageName := word

def snippetKind : Parser Kind := do
  (pstring "broken" *> pure .broken)
  <|> (pstring "fixed" *> pure .fixed)

def name : Parser String :=
  skipChar '(' *> optional ws *> skipString "name" *> ws *> skipString ":=" *> ws *>
  word
  <* optional ws <* skipChar ')'

def attr : Parser (Kind ⊕ String) :=
  .inl <$> snippetKind <|> .inr <$> name

def infoString : Parser ErrorExplanationCodeInfo := do
  let lang ← languageName
  let attrs ← Parsec.many (ws *> attr)
  let mut kind? := Option.none
  let mut name? := Option.none
  for attr in attrs do
    match attr with
    | .inl k =>
      if kind?.isNone then
        kind? := some k
      else
        Parsec.fail "redundant kind specifications"
    | .inr n =>
      if name?.isNone then
        name? := some n
      else
        Parsec.fail "redundant name specifications"
  return { lang, name?, kind? }

end Parse

def parse (s : String) : Except String ErrorExplanationCodeInfo :=
  Parse.infoString.run s |>.mapError (fun s => s!"Invalid code block info string: {s}")

end ErrorExplanationCodeInfo

section LeanRendering


open Verso Genre Manual SubVerso Highlighting

deriving instance Repr for Parser.ModuleParserState

-- FIXME: the returned syntax is incomplete
def runMWE (input : String) : MetaM (Command.State × Parser.InputContext × Array (Syntax ⊕ Substring)) := do
  let fileName   := "<input>"
  let inputCtx   := Parser.mkInputContext input fileName
  let (hdrStx, s, msgs) ← Parser.parseHeader inputCtx
  let (env, msgs) ← processHeader hdrStx {} msgs inputCtx
  -- logInfo m!"Messages: {← msgs.toArray.mapM fun d => d.toString}"
  let cmdState := Command.mkState env msgs

  let shouldElab := !msgs.hasErrors
  let mut (cmdState, stxs) ← processCommands inputCtx s cmdState shouldElab

  -- unless hdrStx.getHeadInfo matches .none do
  stxs := #[hdrStx] ++ stxs
  let stxOrStrs ← addMissingSubstrs stxs inputCtx
  -- TODO: if errors present in `msgs` here, abort
  -- let st ← IO.processCommands inputCtx s (Command.mkState env {} {})
  return (cmdState, inputCtx, stxOrStrs)
where
  processCommands (inputCtx : Parser.InputContext) (s : Parser.ModuleParserState) (cmdState : Command.State) (doElab : Bool) := do
    let mut s := s
    let mut cmdState := cmdState
    -- let mut (stxs : Array (Syntax ⊕ Substring)) := #[]
    let mut stxs := #[]
    repeat
      let scope := cmdState.scopes.head!
      let pmctx : Parser.ParserModuleContext := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
      let (stx, s', msgs') := Parser.parseCommand inputCtx pmctx s cmdState.messages
      -- let mut stxOrStr := .inl st

      -- let last? := if stxs.isEmpty then
      --     some 0
      --   else
      --     match stxs[stxs.size - 1]? with
      --     | some (.inl last) => last.getTrailingTailPos?
      --     | _ => none

      -- -- HACK: Check if the last parse missed some (invalid) syntax and push it as unparsed text
      -- if let some last := last? then
      --   if let some thisHead := stx.getPos? then
      --     if thisHead != last then
      --       let missedStr := Substring.mk inputCtx.input last thisHead
      --       stxs := stxs.push (.inr missedStr)

      -- -- HACK: the highlighter requires everything to be a syntax token, so we dummy-parse non-parseable code into an atom so it renders
      -- if s'.recovering then
      --   let start := s.pos
      --   let fin := s'.pos
      --   let str := Substring.toString ⟨inputCtx.input, start, fin⟩
      --   -- stx := Syntax.atom (SourceInfo.original ⟨inputCtx.input, start, start⟩ start ⟨inputCtx.input, fin, fin⟩ fin) str
      --   -- FIXME: this *still* doesn't work -- the parser might just skip tokens and we lose them...
      --   stxOrStr := .inr str
      --   logInfo m!"Recovering after:\n{s.pos} -> {s'.pos} = {str}"

      s := s'
      cmdState := {cmdState with messages := msgs'}
      -- stxs := stxs.push stxOrStr
      stxs := stxs.push stx
      let cmdCtx : Command.Context := {
        cmdPos       := s.pos
        fileName     := inputCtx.fileName
        fileMap      := inputCtx.fileMap
        snap?        := none
        cancelTk?    := none
      }
      logInfo m!"parsed {stx}"
      if doElab then
        logInfo m!"elaborating {stx}"
        try
          (_, cmdState) ← Command.elabCommandTopLevel stx |>.run cmdCtx |>.run cmdState
        catch e =>
          throwError m!"Error during command elaboration: {e.toMessageData}"
      if Parser.isTerminalCommand stx then
        break
    return (cmdState, stxs)

  addMissingSubstrs (stxs : Array Syntax) (inputCtx : Parser.InputContext) : MetaM (Array (Syntax ⊕ Substring)) := do
    -- HACK: fill in the (malformed) source that was skipped by the parser
    let mut last : String.Pos := 0
    let mut stxOrStrs : Array (Syntax ⊕ Substring) := #[]
    for stx in stxs do
      let some this := stx.getPos?
        | stxOrStrs := stxOrStrs.push (.inl stx)  -- empty headers have no info
          continue
      if this != last then
        let missedStr := Substring.mk inputCtx.input last this
        logInfo m!"Inserting missing:\n• Prev-{last}:{stxOrStrs}\n--> @{last}-{this} {missedStr}\n• @{this}-{stx.getTrailingTailPos?} {stx}"
        stxOrStrs := stxOrStrs.push (.inr missedStr)
      else
        logInfo m!"Syntax correctly follows:\n{stx}"
      stxOrStrs := stxOrStrs.push (.inl stx)
      last := stx.getTrailingTailPos?.getD this
    return stxOrStrs

#eval do
  let mut x := #[1,2]
  let mut i := 0
  while i < x.size do
    let n := x[i]!
    if n == 1 then
      x := x.insertIdx! (i + 1) 37
    IO.println n
    i := i + 1
  IO.println x
-- Note: `runFrontend` outputs the message log to stdout -- not what we want
-- def runMWE (input : String) : MetaM (Command.State × Parser.InputContext × Array Syntax) := do

-- TODO: figure out this snapshot mess
-- def runMWE (input : String) : MetaM ((Command.State × Parser.InputContext × Array Syntax) ⊕ (MessageLog × Parser.InputContext × Syntax)) := do
--   let inputCtx := Parser.mkInputContext input "<input>"
--   let opts := Lean.internal.cmdlineSnapshots.setIfNotSet {} true
--   -- default to async elaboration; see also `Elab.async` docs
--   let opts := Elab.async.setIfNotSet opts true
--   let ctx := { inputCtx with }
--   let processor := Language.Lean.process
--   let snap ← processor (fun _ => pure <| .ok { mainModuleName := .anonymous, opts }) none ctx
--   let snaps := Language.toSnapshotTree snap
--   -- snaps.findInfoTreeAtPos
--   -- let hasErrors ← snaps.runAndReport opts
--   let msgs := snaps.getAll.foldl (· ++ ·.diagnostics.msgLog) {}

--   let some cmdState := Language.Lean.waitForFinalCmdState? snap
--     | throwError m!"Could not fetch final command state for example"
--   logInfo m!"snap: {snap.result?.map (·.processedSnap.stx?)}"

--   Runtime.forget snaps
--   pure <| .inl (cmdState, inputCtx, #[snap.stx])

#eval show MetaM _ from do
  let inputCtx := Parser.mkInputContext "def a := 41
deffoo x := x + 32
def b := 49"
    "<input>"
  let res ← runMWE.processCommands inputCtx {} {
    env := (← getEnv), maxRecDepth := (← MonadRecDepth.getMaxRecDepth)
  } true
  logInfo m!"{res.2}"
  -- let (stx₁, s, msgs) := Parser.parseCommand inputCtx {env := ← mkEmptyEnvironment, options := {}} {} {}
  -- let s₀ := s
  -- logInfo m!"{Substring.mk inputCtx.input 0 s.pos}"
  -- let (stx₂, s, msgs) := Parser.parseCommand inputCtx {env := ← mkEmptyEnvironment, options := {}} s msgs
  -- let msgMsg ← msgs.toList.mapM fun m => m.toString
  -- logInfo <| repr stx₁
  -- logInfo <| repr stx₂
  -- logInfo m!"{Substring.mk inputCtx.input s₀.pos s.pos}"

private def abbrevFirstLine (width : Nat) (str : String) : String :=
  let str := str.trimLeft
  let short := str.take width |>.replace "\n" "⏎"
  if short == str then short else short ++ "…"

private def findMessagesForUnparsedSpan (ictx : Parser.InputContext) (src : Substring) (msgs : Array Message) : IO Highlighted := do
  let msgsHere := msgs.filterMap fun m =>
    let pos := ictx.fileMap.ofPosition m.pos
    let endPos := ictx.fileMap.ofPosition (m.endPos.getD m.pos)
    if src.startPos ≤ pos && pos ≤ src.stopPos then
      some (m, pos, min src.stopPos endPos)
    else
      none

  if msgsHere.isEmpty then
    return .text src.toString

  let mut res := #[]
  for (msg, start, fin) in msgsHere do
    if src.startPos < start then
      let initialSubstr := { src with stopPos := start }
      res := res.push (.text initialSubstr.toString)
    let kind : Highlighted.Span.Kind :=
      match msg.severity with
      | .error => .error
      | .warning => .warning
      | .information => .info
    let content := { src with startPos := start, stopPos := fin }
    res := res.push (.span #[(kind, ← openUntil.contents msg)] (.text content.toString))
    if fin < src.stopPos then
      let finalSubstr := { src with startPos := fin }
      res := res.push (.text finalSubstr.toString)
  return .seq res


def leanMWE : CodeBlockExpander
  | args, str => Manual.withoutAsync <| do
    let config ← LeanBlockConfig.parse.run args

    PointOfInterest.save (← getRef) ((config.name.map toString).getD (abbrevFirstLine 20 str.getString))
      (kind := Lsp.SymbolKind.file)
      (detail? := some ("Lean code" ++ config.outlineMeta))

    let src := str.getString
    let (cmdState, inputCtx, cmds) ← runMWE src
    -- | .inr (msgs, inputCtx, stx) =>
    --   let nonSilentMsgs := msgs.toArray.filter (!·.isSilent)
    --   let hls ← withTheReader Core.Context (fun ctx => { ctx with
    --       fileMap := inputCtx.fileMap
    --       fileName := inputCtx.fileName }) <|
    --     highlight stx nonSilentMsgs {}
    --   let range : Option Lsp.Range := none
    --   if let some name := config.name then
    --     let msgs ← nonSilentMsgs.mapM fun msg => do

    --       let head := if msg.caption != "" then msg.caption ++ ":\n" else ""
    --       let txt := withNewline <| head ++ (← msg.data.toString)

    --       pure (msg.severity, txt)
    --     saveOutputs name msgs.toList
    --   pure #[← ``(Block.other (Block.lean $(quote hls) (some $(quote (← getFileName))) $(quote range)) #[Block.code $(quote str.getString)])]



    -- logInfo m!"running mwe"
    -- let (cmdState, str', inputCtx) ← runMWE src
    -- logInfo m!"got result:\n{← cmdState.infoState.trees[0]!.format}"
    -- -- logInfo m!"got result:\n{cmdState.env.constants.map₂.toList.map fun d => d.1}"

    -- let (testEnv, testSucc) ← runFrontend src {} "<input>" .anonymous
    -- logInfo m!"Test result: success {testSucc} with {testEnv.constants.map₂.toList.map fun d => d.1}"

    let mut hls := Highlighted.empty
    let nonSilentMsgs := cmdState.messages.toArray.filter (!·.isSilent)
    -- logInfo m!"Messages: {← cmdState.messages.toList.mapM (·.toString)}"
    -- logInfo m!"Info trees: {← cmdState.infoState.trees.toList.mapM (·.format)}"
    for cmd in cmds do
      -- hls := hls ++ (← withTheReader Core.Context (fun ctx => {
      --   ctx with
      --   fileMap := inputCtx.fileMap
      --   fileName := inputCtx.fileName }) <|
      -- highlight cmd nonSilentMsgs cmdState.infoState.trees)
      let hl ←
        match cmd with
        | .inl cmd => withTheReader Core.Context (fun ctx => { ctx with
                fileMap := inputCtx.fileMap
                fileName := inputCtx.fileName }) <|
              highlight cmd nonSilentMsgs cmdState.infoState.trees
        | .inr cmd =>
          findMessagesForUnparsedSpan inputCtx cmd nonSilentMsgs
          -- pure <| Highlighted.text cmd.toString
      hls := hls ++ hl

    let range : Option Lsp.Range := none
    if let some name := config.name then
      let msgs ← nonSilentMsgs.mapM fun msg => do

        let head := if msg.caption != "" then msg.caption ++ ":\n" else ""
        let txt := withNewline <| head ++ (← msg.data.toString)

        pure (msg.severity, txt)
      saveOutputs name msgs.toList
    pure #[← ``(Block.other (Block.lean $(quote hls) (some $(quote (← getFileName))) $(quote range)) #[Block.code $(quote str.getString)])]
where
  withNewline (str : String) := if str == "" || str.back != '\n' then str ++ "\n" else str


run_meta do
  let src := "
def x := 15
deffoo := 13
def y := 71



def z := true"
  let inputCtx := Parser.mkInputContext src "<input>"
  let (stx, s, msgs) := Parser.parseCommand inputCtx { env := (← getEnv), options := {} } {} {}
  let (stx', s, msgs) := Parser.parseCommand inputCtx { env := (← getEnv), options := {} } s msgs
  let (stx'', s, msgs) := Parser.parseCommand inputCtx { env := (← getEnv), options := {} } s msgs
  -- logInfo m!"{(stx, stx', ← msgs.toList.mapM (·.toString))}"
  logInfo m!"{(stx.getPos?, stx.getTailPos?, stx'.getPos?, stx'.getTailPos?, stx''.getPos?, stx''.getTailPos?)}"
  logInfo (stx ++ stx' ++ stx'')


end LeanRendering

def tryElabErrorExplanationCodeBlock (info? _ : Option String) (str : String) : DocElabM Term := do
  if let some info := info? then
    let { lang, name?, kind? } ← match ErrorExplanationCodeInfo.parse info with
      | .ok x => pure x
      | .error e => throwError e
    if lang == "output" then
      let some name := name? | throwError "output is missing name"
      let some kind := kind? | throwError "output is missing kind"
      -- TODO: account for multiple and unify with below case
      let name := name ++ if kind == .broken then "Broken" else "Fixed"
      let args := #[(← `(argument| $(mkIdent name.toName):ident))]
      let parsedArgs ← parseArgs args
      let blocks ← withFreshMacroScope <| leanOutput parsedArgs (quote str)
      return (← ``(Verso.Doc.Block.concat #[$blocks,*]))
    else
      -- Assume all unlabeled code is Lean
      let mut args := #[]
      if let some name := name? then
        let mut name := name
        if let some kind := kind? then
          name := name ++ if kind == .broken then "Broken" else "Fixed"
        -- TODO: allow for multiple fixed (and maybe also broken?) versions
        args := args.push (← `(argument| name := $(mkIdent name.toName):ident))
      if let some kind := kind? then
        let errorVal ← if kind == .broken then `(arg_val|true) else `(arg_val|false)
        args := args.push (← `(argument| error := $errorVal))
      let parsedArgs ← parseArgs args
      -- FIXME: this hack doesn't seem like it's going to work because `lean` cares about
      -- actual source positions (Q: how was this working before?)
      -- let stx : Syntax := Syntax.copyHeadTailInfoFrom (← getRef) (quote (k := `str) str)
      -- Without the above, all errors/warnings get logged at pos 0 in the editor:
      let blocks ← withFreshMacroScope <| leanMWE parsedArgs (quote str)
      return (← ``(Verso.Doc.Block.concat #[$blocks,*]))
  ``(Verso.Doc.Block.code $(quote str))

def blockFromMarkdownWithLean (b : MD4Lean.Block) : DocElabM Term := do
  unless (← Docstring.getElabMarkdown) do
    return (← Markdown.blockFromMarkdown b (handleHeaders := Markdown.strongEmphHeaders))
  let tactics ← Elab.Tactic.Doc.allTacticDocs
  let keywords := tactics.map (·.userName)
  let ref ← getRef
  -- It'd be silly for some weird edge case to block on this feature...
  let s ← (saveState : TermElabM _)
  let (t, outputs) ←
    try
      let res ←
        blockFromMarkdown b
          (handleHeaders := Markdown.strongEmphHeaders)
          (elabInlineCode := tryElabInlineCode tactics keywords)
          (elabBlockCode := fun i l s => withRef ref <| tryElabErrorExplanationCodeBlock i l s)
          -- (elabBlockCode := tryElabErrorExplanationCodeBlock)
      synthesizeSyntheticMVarsUsingDefault
      pure (res, leanOutputs.getState (← getEnv))
    finally
      -- TODO: this logic is now inappropriate because it's swallowing elab errors
      let { messages, .. } ← getThe Core.State
      s.restore
      modifyThe Core.State fun s => { s with messages }
  modifyEnv (leanOutputs.setState · outputs)
  return t

/-- The code contents of an example, not including any subsequent description. -/
private structure ExampleContents where
  name : String
  title : Array Term
  body : Array Term

inductive ExampleState
  | beforeExamples
  | inExamples
  | pastHeader (title : Array Term)
  | pastBroken (info : ExampleContents)
  | pastFixed (info : ExampleContents)
  | pastOutput (info : ExampleContents)
  | afterExamples

def ExampleState.describe : ExampleState → String
  | .beforeExamples => "the 'Examples' header has not yet been reached"
  | .inExamples => "found the 'Examples' header, but no example was encountered"
  | .pastHeader _ => s!"found an example header but no code blocks"
  | .pastBroken _ => s!"found the broken code block but none after"
  | .pastFixed _ => s!"found the broken and fixed code blocks but none after"
  | .pastOutput _ => s!"found all of the code blocks and reading description"
  | .afterExamples => s!"passed the examples section and moved to a new top-level header"

abbrev ExplanationElabM := StateT ExampleState DocElabM

private def examplesHeader := "Examples"

private def infoOfCodeBlock : MD4Lean.Block → Except String ErrorExplanationCodeInfo
  | .code info _ _ _ => do
    let txt ← attr' info
    ErrorExplanationCodeInfo.parse txt
  | el => .error s!"block element is not a code block but instead:\n{repr el}"

private def infoOfCodeBlock? : MD4Lean.Block → Option ErrorExplanationCodeInfo
  | .code info _ _ _ => do
    let txt ← (attr' info).toOption
    ErrorExplanationCodeInfo.parse txt |>.toOption
  | _ => none

-- TODO: register the proper monad lift instance to get rid of all these matches
private def expectExplanationCodeInfo
    (b : MD4Lean.Block) (expLang : String) (expKind : ErrorExplanationCodeInfo.Kind)
    (expName? : Option String := none)
  : DocElabM Unit := do
  let { name?, kind?, lang } ← match infoOfCodeBlock b with
    | .ok x => pure x
    | .error e => throwError e
  unless lang == expLang do
    throwError "Expected a code block with language '{expLang}', but found '{lang}'"
  if let some expName := expName? then
    unless name? == some expName do
      throwError "Expected a code block of name '{expName}', but found {name?.map (m!"'{·}'") |>.getD "anonymous"}"
  unless kind? == some expKind do
    let str := kind?.map toString |>.getD "unspecified"
    throwError "Expected a code block of kind '{expKind}', but found '{str}'"

-- FIXME: do this properly
private def termsOfTexts (txts : Array Text) : DocElabM (Array Term) := do
  let (stxs, _) ← (txts.mapM (inlineFromMarkdown ·)).run' none {
    elabInlineCode := tryElabInlineCode #[] #[]
    headerHandlers := ⟨Markdown.strongEmphHeaders⟩,
    elabBlockCode := tryElabBlockCode
  } {}
  return stxs

private def isExamplesHeaderText (txt : Array Text) : Bool :=
  if _ : txt.size = 1 then
    match txt[0] with
    | .normal str => str.trim == "Examples"
    | _ => false
  else false

-- TODO: Add PoI like the real elaborator does
private def makeExample (contents : ExampleContents) : DocElabM Term :=
  let {title, body, ..} := contents
  ``(Block.other (Block.example none (opened := true))
            #[Block.para #[$title,*], $body,*])

private def nameOfCodeBlock? (b : MD4Lean.Block) : Option String :=
  infoOfCodeBlock? b >>= (·.name?)

-- FIXME: actually do this properly; for now, a dummy implementation
private def makeExampleLayout (codeBlocks : Array Term) : DocElabM Term := do
  ``(Verso.Doc.Block.concat #[$codeBlocks,*])

-- TODO: we no longer need to worry about names if we're going to just enforce sequentiality of blocks
-- TODO: allow for fixed output as well as broken output?
-- TODO: if we do keep names around, scope all names to the current error explanation name so that two
--       explanations using the same name doesn't break stuff
def processExplanationBlock (block : MD4Lean.Block) : ExplanationElabM (Option Term) := do
  if let MD4Lean.Block.header 1 txt := block then
    if isExamplesHeaderText txt then
      unless (← get) matches .beforeExamples do
        throwError "Found a duplicate 'Examples' header: There should be only one 'Examples' section per explanation"
      set ExampleState.inExamples
    else
      let exampleState : ExampleState := if (← get) matches .beforeExamples then
        .beforeExamples
      else .afterExamples
      set exampleState
  else
    match (← get) with
    -- While inside an example, we do not return any elements but instead
    -- accumulate the in-progress element in the state
    | .pastHeader title =>
      expectExplanationCodeInfo block "lean" .broken
      let term ← _root_.blockFromMarkdownWithLean block
      let some name := nameOfCodeBlock? block
        | throwError m!"Missing name in example code block under header: {title}"
      set <| ExampleState.pastBroken { name, title, body := #[term] }
      return none
    | .pastBroken {name, title, body} =>
      expectExplanationCodeInfo block "lean" .fixed name
      let term ← _root_.blockFromMarkdownWithLean block
      set <| ExampleState.pastFixed {name, title, body := body.push term}
      return none
    | .pastFixed {name, title, body} =>
      expectExplanationCodeInfo block "output" .broken name
      let term ← _root_.blockFromMarkdownWithLean block
      -- Combine all code blocks into the example layout
      let codeLayout ← makeExampleLayout (body.push term)
      set <| ExampleState.pastOutput {name, title, body := #[codeLayout]}
      return none
    | .pastOutput {name, title, body} =>
      if let .header 2 txts := block then
        -- At the start of the next example, finalize and return the current one
        let newTitle ← termsOfTexts txts
        set <| ExampleState.pastHeader newTitle
        return (← makeExample {name, title, body})
      else
        -- We allow arbitrary description up to the next header
        let term ← _root_.blockFromMarkdownWithLean block
        set <| ExampleState.pastOutput {name, title, body := body.push term}
        return none
    | .inExamples =>
      if let .header 2 txts := block then
        let title ← termsOfTexts txts
        set <| ExampleState.pastHeader title
        return none
      else
        throwError "Found something other than a level-2 example header immediately following the start of the 'Examples' section"
    | _ => pure ()
  _root_.blockFromMarkdownWithLean block


def processExplanationBlocks (blocks : Array MD4Lean.Block) : DocElabM (Array (TSyntax `term)) := do
  let mut (terms, state) ← (blocks.filterMapM processExplanationBlock).run .beforeExamples
  -- The last example will not have finished elaborating; finish it:
  match state with
  | .pastOutput {name, title, body} =>
    terms := terms.push (← makeExample {name, title, body})
  | .beforeExamples | .afterExamples => pure ()
  | st => throwError m!"Incomplete final example; finished in the following state: {st.describe}"
  return terms

def processExplanationMetadata (name : Name) (metadata : ErrorExplanation.Metadata) : DocElabM (Array (TSyntax `term)) := do
  -- TODO: how do we push a header? For now, just bold...
  let nameBlock ← ``(Verso.Doc.Block.para #[Verso.Doc.Inline.bold #[Verso.Doc.Inline.text $(quote name.toString)]])
  let summaryBlock ← ``(Verso.Doc.Block.para #[Verso.Doc.Inline.text $(quote metadata.summary)])
  let otherBlocks := #[("Severity: ", if metadata.severity == .error then "Error" else "Warning"),
                       ("Since: ", metadata.sinceVersion)]
  let removedBlocks := metadata.removedVersion.map (fun v => #[("Removed: ", v)]) |>.getD #[]
  let otherBlocks ← (otherBlocks ++ removedBlocks).mapM fun (label, datum) =>
    ``(Inline.concat #[Inline.bold #[Inline.text $(quote label)], Inline.text $(quote datum)])
  let otherBlock ← ``(Doc.Block.para #[$otherBlocks,*])
  return #[nameBlock, otherBlock, summaryBlock]

structure ExplanationConfig where
  name : Ident

variable [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] in
def ExplanationConfig.parser : ArgParse.ArgParse m ExplanationConfig :=
  ExplanationConfig.mk <$> .positional `name {
    description := "name of error whose explanation to display",
    get := fun
      | .name x => pure x
      | other => throwError "Expected error name, got {repr other}"
  }

def explanationBlockFor (name : Name) : DocElabM (Array Term) := do
  let explan? ← getErrorExplanation? name
  -- Doc.PointOfInterest.save (← getRef) name.toString (detail? := some "Documentation")
  let blockStx ←
    match explan? with
    | .none =>
      pure #[← ``(Verso.Doc.Block.para #[Verso.Doc.Inline.text s!"Could not find explanation for '{$(quote name)}'"])]
    | some explan =>
      try
        let some ast := MD4Lean.parse explan.doc
          | throwErrorAt (← getRef) "Failed to parse docstring as Markdown"
        let bodyBlocks ← processExplanationBlocks ast.blocks
        let metadataBlocks ← processExplanationMetadata name explan.metadata
        return metadataBlocks ++ bodyBlocks
      catch
        | .error ref msg => throw <| .error ref m!"Failed to process explanation for {name}: {msg}"
        | e => throw e
  return blockStx

@[block_role_expander explanation]
def explanation : BlockRoleExpander
  | args, #[] => do
    let config ← ExplanationConfig.parser.run args
    explanationBlockFor config.name.getId
  | _, _ => throwError "unexpected syntax"


end MyImpl

#doc (Manual) "Diagnostic Explanation" =>

This is a test!

:::example "This is an example" (opened := true)

You should look at this example!

:::

**Demo**

```lean (name := helloDemo) (error := true)
def cf x := 32
```

```leanOutput helloDemo
failed to infer binder type
```

```lean (name := helloDemoFixed)
def cf (x : Nat) := 32
```

Checking rewrite:

```lean (error := true)
example (v : Vector Nat n) (h : n = 1) : v = v := by
  rewrite [h]
```

IO Lean:

::::example "IO Lean example" (opened := true)
:::ioExample
```ioLean
def x := 47
def y : UInt32 := dbg_trace 42; 47
def main : IO UInt32 := do
  pure (y - 47)
```

```stderr
42
```
:::
::::

**Actual**

{explanation Lean.MotiveNotTypeCorrect}

{explanation BadDocstring2}

{explanation BadImport}

{docstring badExDocstring}

-- explanation Lean.MyGreatTypeCorrectGoal

-- TODO: change tracking reference of main to jrr6
