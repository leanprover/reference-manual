import VersoManual
import VersoManual.InlineLean
import Manual.Meta.ErrorExplanation
import Verso.Doc.Elab

open Lean
set_option doc.verso true
variable [Monad m] [MonadError m]
set_option pp.rawOnError true
structure ErrorExampleConfig where
  title : String
instance : Verso.ArgParse.FromArgs ErrorExampleConfig m where
  fromArgs :=
    ErrorExampleConfig.mk <$> Verso.ArgParse.positional `title Verso.ArgParse.ValDesc.string

/--
Structured examples that show a minimum working example (MWE) of an error, as well as one or more
corrections, in a fashion suitable for error explanations. The structure is relatively rigid:

 * One code block labeled "broken" containing Lean code that generates an error
 * One code block labeled "output" that contains the plan text of (one of the) generated errors
 * One or more code blocks labeled "fixed" that contain Lean code demonstrating how the error can
   be corrected. If there is more than one block, the block must have an additional positional
   argument, a string describing the example. (A block labeled {lit}`fixed "descr"` will be
   displayed as "Fixed (descr).")

**Example:**
`````
:::errorExample "Only a Dot Before the Numeral"
```broken
example := .3
```
```output
invalid occurrence of `·` notation, it must be surrounded by parentheses (e.g. `(· + 1)`)
```
```fixed "make it an `Nat`"
example := 3
```
```fixed "make it a `Float`"
example := 0.3
```
Some explanatory text here.
:::
`````
-/
@[directive]
def errorExample : Verso.Doc.Elab.DirectiveExpanderOf ErrorExampleConfig
  | { title }, contents => do
    let brokenStx :: restStx := contents.toList
      | throwError m!"The error example had no contents"
    let `(Lean.Doc.Syntax.codeblock|``` broken| $brokenTxt ```) := brokenStx
      | throwErrorAt brokenStx m!"First element in errorExample must be a `broken` codeblock containing the broken minimal working example"

    let errorStx :: restStx := restStx
      | throwError m!"The error example did not contain a second element"
    let `(Lean.Doc.Syntax.codeblock|``` output| $errorTxt ```) := errorStx
      | throwErrorAt errorStx m!"Second element in errorExample must be an `output` codeblock containing the generated error message"

    let block ← Verso.Genre.Manual.InlineLean.lean { «show» := true, keep := false, name := `bork, error := true, fresh := true } brokenTxt
    let (fixedExamples, restStx) ← partitionFixed restStx
    let examples ← match fixedExamples with
      | [] => throwErrorAt restStx[0]! "Error examples must include one or more `fixed` codeblocks containing a fix for broken code"
      | [(_, .none, fixedTxt)] => Verso.Genre.Manual.InlineLean.lean { «show» := true, keep := false, name := none, error := false, fresh := true } brokenTxt
      | [(_, .some title, _)] => throwErrorAt title m!"Error explanations with a single title don't need to name the title"
      | _ =>
        discard fixedExamples.mapM (fun (_, ))

    let str := s!"{repr contents}"
    ``(Doc.Block.para #[Doc.Inline.text $(quote (repr block).pretty)])
where
  partitionFixed (blocks: List (TSyntax `block)) : Verso.Doc.Elab.DocElabM (List (Syntax, Option StrLit × TSyntax `str) × List (TSyntax `block)) := do
  match blocks with
  | [] => throwError "No description blocks at the end of error explanation"
  | block :: rest =>
    let `(Lean.Doc.Syntax.codeblock|``` fixed $args*| $fixedTxt ```) := block
      | return ([], blocks)
    let parsedArgs ← Verso.Doc.Elab.parseArgs args
    let arg? : Option _ ← match parsedArgs.toList with
      | [] => pure none
      | [.anon (.str title)] => pure <| some title
      | [_] => throwErrorAt args[0]! m!"String arg expected"
      | _ => throwErrorAt args[1]! m!"At most one string arg expected"
    logInfoAt block m!".. {repr args}"
    let (fixedExamples, descrBlocks) ← partitionFixed rest
    return ((block, arg?, fixedTxt) :: fixedExamples, descrBlocks)
/-
    | `(Lean.Doc.Syntax.codeblock|``` fixed $arg?| $fixedTxt ```) :: restStx => do
      let (fixedExamples, docs) ← partitionFixed restStx
      return ((arg, fixedTxt), docs)
    | restStx => pure ([], restStx)-/


#doc (Verso.Genre.Manual) "Example" =>

:::errorExample "Only a Dot Before the Numeral"
```broken
example := .3
```
```output
invalid occurrence of `·` notation, it must be surrounded by parentheses (e.g. `(· + 1)`)
```
```fixed "make it an `Nat`"
example := 3
```
```fixed "make it a `Float`"
example := 0.3
```
```fixed
example := 0.3
```
Some explanatory text here.
:::
