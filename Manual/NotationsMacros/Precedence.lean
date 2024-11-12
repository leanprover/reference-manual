/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "Precedence" =>
%%%
tag := "precedence"
%%%

Infix operators, notations, and other syntactic extensions to Lean make use of explicit {tech}[precedence] annotations.
While precedences in Lean can technically be any natural number, by convention they range from {evalPrec}`min` to {evalPrec}`max`, respectively denoted `min` and `max`.{TODO}[Fix the keywordOf operator and use it here]
Function application has the highest precedence.

:::syntax prec (open := false)
Most operator precedences consist of explicit numbers.
The named precedence levels denote the outer edges of the range, close to the minimum or maximum, and are typically used by more involved syntax extensions.
```grammar
$n:num
```

Precedences may also be denoted as sums or differences of precedences; these are typically used to assign precedences that are relative to one of the named precedences.
```grammar
$p + $p
```
```grammar
$p - $p
```
```grammar
($p)
```

The maximum precedence is used to parse terms that occur in a function position.
Operators should typically not use use this level, because it can interfere with users' expectation that function application binds more tightly than any other operator, but it is useful in more involved syntax extensions to indicate how other constructs interact with function application.
```grammar
max
```

Argument precedence is one less than the maximum precedence.
This level is useful for defining syntax that should be treated as an argument to a function, such as {keywordOf Lean.Parser.Term.fun}`fun` or {keywordOf Lean.Parser.Term.do}`do`.
```grammar
arg
```

Lead precedence is less that argument precedence, and should be used for custom syntax that should not occur as a function argument, such as {keywordOf Lean.Parser.Term.let}`let`.
```grammar
lead
```

The minimum precedence can be used to ensure that an operator binds less tightly than all other operators.
```grammar
min
```
:::
