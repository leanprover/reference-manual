import VersoManual

import Manual.Meta

open Verso.Genre Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "Terms" =>

::: planned
This chapter will describe Lean's term language, including the following features:
 * Name resolution, including variable occurrences, `open` declarations and terms
 * Function application, including implicit, instance, and named arguments
 * Leading `.`-notation and accessor notation
 * `fun`, with and without pattern matching
 * Literals (some via cross-references to the appropriate types, e.g. {name}`String`)
 * Conditionals and their relationship to {name}`Decidable`
 * Pattern matching, including `match`, `let`, `if let`, `matches`, `nomatch`, `nofun`
 * Do-notation, including `let mut`, `for`, `while`, `repeat`, `break`, `return`
:::