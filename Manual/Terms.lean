import VersoManual

import Manual.Meta

open Verso.Genre Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "Terms" =>

::: planned 66
This chapter will describe Lean's term language, including the following features:
 * Name resolution, including variable occurrences, `open` declarations and terms
 * Function application, including implicit, instance, and named arguments
 * Leading `.`-notation and accessor notation
 * `fun`, with and without pattern matching
 * Literals (some via cross-references to the appropriate types, e.g. {name}`String`)
 * Conditionals and their relationship to {name}`Decidable`
 * Pattern matching, including `match`, `let`, `if let`, `matches`, `nomatch`, `nofun`
 * Do-notation, including `let mut`, `for`, `while`, `repeat`, `break`, `return`
 * {deftech}_Holes_ and {deftech}_named holes_
 * The various forms of reduction:
   : β (beta)

    Applying a `fun`-term to an argument by substitution for the bound variable

   : δ (delta)

    Replacing occurrences of defined names by the definition's value

   : ι (iota)

    Reduction of recursors whose targets are constructors

   : ζ (zeta)

     Replacement of let-bound variables by their defined values
:::
