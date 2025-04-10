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

/--
# Sample explanation

This error appears when things go wrong.

### Example

If we fail to give a type to our binder, we get the error:

```lean broken (name := hello)
def f x := 32
```
```output broken (name := hello)
failed to infer binder type
```

We can fix this by typing our binder:
```lean fixed (name := hello)
def f (x : Nat) := 32
```
-/
def badExDocstring2 := ()

section MyImpl

open Std.Internal Lean Elab Term Verso Doc Elab Genre Manual Markdown MD4Lean

inductive ErrorExplanationCodeInfo.Kind
  | broken | fixed
deriving Repr, Inhabited, BEq

structure ErrorExplanationCodeInfo where
  lang : String
  kind? : Option ErrorExplanationCodeInfo.Kind
  name? : Option String
deriving Repr

namespace ErrorExplanationCodeInfo
open Parsec Parsec.String

namespace Parse

def skipWss : Parser Unit :=
  many1 ws *> pure ()

def word : Parser String := fun it =>
  let it' := it.find (·.isWhitespace)
  .success it' (it.extract it')

def languageName := word

def snippetKind : Parser Kind := do
  (pstring "broken" *> pure .broken)
  <|> (pstring "fixed" *> pure .fixed)

def name : Parser String :=
  skipChar '(' *> skipString "name" *> skipWss *> skipString ":=" *> skipWss *>
  word
  <* skipWss <* skipChar ')'

def attr : Parser (Kind ⊕ String) :=
  .inl <$> snippetKind <|> .inr <$> name

def infoString : Parser ErrorExplanationCodeInfo := do
  let lang ← languageName
  let attrs ← Parsec.many (skipWss *> attr)
  let mut kind? := Option.none
  let mut name? := Option.none
  for attr in attrs do
    match attr with
    | .inl k =>
      if kind?.isNone then
        kind? := some k
      else
        failure
    | .inr n =>
      if name?.isNone then
        name? := some n
      else
        failure
  return { lang, name?, kind? }

end Parse

def parse (s : String) : Option ErrorExplanationCodeInfo :=
  Parse.infoString.run s |>.toOption

-- #eval parse "lean broken (name := hello)"

end ErrorExplanationCodeInfo

def tryElabErrorExplanationCodeBlock (info? _ : Option String) (str : String) : DocElabM Term := do
  if let some info := info? then
    if let some { lang, name?, kind? } := ErrorExplanationCodeInfo.parse info then
      if lang == "lean" then
        let isErrorTemp := kind? == some .broken
        let mut args := #[]
        if let some name := name? then
          args := args.push (← `(argument| name := $(mkIdent name.toName):ident))
        if isErrorTemp then
          args := args.push (← `(argument| error := true))
        let parsedArgs ← parseArgs args
        -- let isErrorTemp := kind? == some .broken
        -- let stx ← getRef
        -- -- TODO: including the args breaks the block -- I assume they must be malformed
        -- -- (if you take args = #[], this works)
        -- let mut args := #[
        --   .named stx (mkIdent `error) (.str (quote (toString isErrorTemp)))
        -- ]
        -- if let some name := name? then
        --   args := args.push <| .named stx (mkIdent `nme) (.name (mkIdent name.toName))
        let blocks ← withFreshMacroScope <| lean parsedArgs (quote str)
        let blocks := blocks.push (← ``(Verso.Doc.Block.para <| $(quote (name?.getD "nameless" ++ " " ++ lang)) ++ " this is a codeblock"))
        ``(Verso.Doc.Block.concat #[$blocks,*])
      else if lang == "output" then
        try
          let some name := name? | throwError "output is missing name"
          let args := #[(← `(argument| $(mkIdent name.toName):ident))]
          let parsedArgs ← parseArgs args
          let blocks ← withFreshMacroScope <| leanOutput parsedArgs (quote str)
          let blocks := blocks.push (← ``(Verso.Doc.Block.para <| $(quote name) ++ " this is an output!"))
          ``(Verso.Doc.Block.concat #[$blocks,*])
        catch _ =>
          ``(Verso.Doc.Block.para "output rendering did not work")
      else
        ``(Verso.Doc.Block.code $(quote "something went wrong1"))
        -- throwError "unexpected code block language {lang}"
      -- ``(Verso.Doc.Block.concat #[Verso.Doc.Block.code $(quote str),
      --     Verso.Doc.Block.code $(quote lang),
      --     Verso.Doc.Block.code $(quote <| name?.getD "anonymous"),
      --     Verso.Doc.Block.code $(quote <| ((toString ∘ repr) <$> kind?).getD "kindless")])
    else
      ``(Verso.Doc.Block.code $(quote "something went wrong2"))
      -- throwError "Malformed info string in code block: {info}"
  else
    ``(Verso.Doc.Block.code $(quote "something went wrong3"))

def blockFromMarkdownWithLean (names : List Name) (b : MD4Lean.Block) : DocElabM Term := do
  unless (← Docstring.getElabMarkdown) do
    return (← Markdown.blockFromMarkdown b (handleHeaders := Markdown.strongEmphHeaders))
  let tactics ← Elab.Tactic.Doc.allTacticDocs
  let keywords := tactics.map (·.userName)
  try
    match names with
    | decl :: decls =>
      -- This brings the parameters into scope, so the term elaboration version catches them!
      Meta.forallTelescopeReducing (← getConstInfo decl).type fun _ _ =>
        blockFromMarkdownWithLean decls b
    | [] =>
      -- It'd be silly for some weird edge case to block on this feature...
      let rec loop (max : Nat) (s : SavedState) : DocElabM Term := do
        match max with
        | k + 1 =>
          try
            let res ←
              blockFromMarkdown b
                (handleHeaders := Markdown.strongEmphHeaders)
                (elabInlineCode := tryElabInlineCode tactics keywords)
                (elabBlockCode := tryElabErrorExplanationCodeBlock)
            synthesizeSyntheticMVarsUsingDefault

            discard <| addAutoBoundImplicits #[] (inlayHintPos? := none)

            return res
          catch e =>
            if let some n := isAutoBoundImplicitLocalException? e then
              s.restore (restoreInfo := true)
              Meta.withLocalDecl n .implicit (← Meta.mkFreshTypeMVar) fun x =>
                withTheReader Term.Context (fun ctx => { ctx with autoBoundImplicits := ctx.autoBoundImplicits.push x } ) do
                  loop k (← (saveState : TermElabM _))
            else throw e
        | 0 => throwError "Ran out of local name attempts"
      let s ← (saveState : TermElabM _)
      try
        loop 40 s
      finally
        (s.restore : TermElabM _)
  catch _ =>
    Markdown.blockFromMarkdown b
      (handleHeaders := Markdown.strongEmphHeaders)

@[block_role_expander myblock]
def myblock : BlockRoleExpander
  | #[], #[] => do
    let str? ← getDocString? (← getEnv) ``badExDocstring2
    -- Doc.PointOfInterest.save (← getRef) name.toString (detail? := some "Documentation")
    let blockStx ←
      match str? with
      | .none => pure #[]
      | some docs =>
        let some ast := MD4Lean.parse docs
          | throwErrorAt (← getRef) "Failed to parse docstring as Markdown"
        ast.blocks.mapM (_root_.blockFromMarkdownWithLean [``badExDocstring2])
    return blockStx
  | _, _ => throwError "unexpected syntax"


end MyImpl

#doc (Manual) "Diagnostic Explanations" =>
# Explanations
%%%
tag := "diagnostics"
number := false
%%%

This is a test!

:::example "This is an example" (opened := true)

You should look at this example!

:::

## Demo

```lean (name := helloDemo) (error := true)
def f x := 32
```
```leanOutput helloDemo
failed to infer binder type
```

```lean (name := helloDemoFixed)
def f (x : Nat) := 32
```

## Actual

{myblock}

{docstring badExDocstring}

{docstring badExDocstring2}

{docstring Option.forM}

-- TODO: change tracking reference of main to jrr6
