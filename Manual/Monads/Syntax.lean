/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Papers

import Manual.NotationsMacros.Operators
import Manual.NotationsMacros.Precedence
import Manual.NotationsMacros.Notations
import Manual.NotationsMacros.SyntaxDef

import Lean.Parser.Command

open Manual

open Verso.Genre
open Verso.Genre.Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "Syntax" =>


# Infix Operators

:::syntax term
```grammar
$_ >>= $_
```
```grammar
$_ =<< $_
```

```grammar
$_ >=> $_
```
```grammar
$_ <=< $_
```

```grammar
$_ <$> $_
```

```grammar
$_ <&> $_
```

```grammar
$_ <*> $_
```

```grammar
$_ *> $_
```

```grammar
$_ <* $_
```

:::

# `do`-Notation
%%%
tag := "do-notation"
%%%

# Iteration

{docstring ForIn}

{docstring ForIn'}

{docstring ForM}

{docstring ForM.forIn}
