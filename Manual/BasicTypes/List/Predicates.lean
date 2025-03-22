/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

open Manual.FFIDocType

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Predicates and Relations" =>

{docstring List.IsPrefix}

:::syntax term (title := "List Prefix")
```grammar
$_ <+: $_
```

{includeDocstring List.«term_<+:_»}

:::

{docstring List.IsSuffix}

:::syntax term (title := "List Suffix")
```grammar
$_ <:+ $_
```

{includeDocstring List.«term_<:+_»}

:::

{docstring List.IsInfix}

:::syntax term (title := "List Infix")
```grammar
$_ <:+: $_
```

{includeDocstring List.«term_<:+:_»}

:::

{docstring List.Sublist}

::: syntax term (title := "Sublists") (namespace := List)
```grammar
$_ <+ $_
```

{includeDocstring List.«term_<+_»}

This syntax is only available when the `List` namespace is opened.
:::

{docstring List.Perm}

:::syntax term (title := "List Permutation") (namespace := List)
```grammar
$_ ~ $_
```

{includeDocstring List.«term_~_»}

This syntax is only available when the `List` namespace is opened.
:::

{docstring List.Pairwise}

{docstring List.Nodup}

{docstring List.Lex}

{docstring List.Mem}
