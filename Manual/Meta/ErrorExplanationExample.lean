import VersoManual
import VersoManual.InlineLean
import Manual.Meta.ErrorExplanation

open Lean
set_option doc.verso true
variable [Monad m] [MonadError m]

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

    let str := s!"{repr contents}"
    ``(Doc.Block.para #[Doc.Inline.text $(quote (repr block).pretty)])


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
Some explanatory text here.
:::
