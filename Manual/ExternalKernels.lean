/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leo de Moura, Kim Morrison
-/

import VersoManual

import Lean.Parser.Term

import Manual.Meta

-- Needed for the if-then-else normalization example.
import Std.Data.TreeMap
import Std.Data.HashMap

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Doc.Elab (CodeBlockExpander)
open Verso.Code.External


set_option pp.rawOnError true

set_option linter.typography.quotes true
set_option linter.typography.dashes true


open Manual (comment)

#doc (Manual) "External Kernels" =>
%%%
tag := "external-kernels"
htmlSplit := .never
%%%

Lean is both a proof assistant with powerful automation and an extensible, full-featured programming language.
However, all theorems that can be proved in Lean are translated by the {tech}[elaborator] to a much smaller {ref "type-system"}[core type theory].
The Lean {tech}[kernel] is a small, robust checker for this core theory.

As described in {ref "validating-proofs"}[the chapter on validating Lean proofs], Lean is designed so that its core theory can also be checked by independently implemented kernels.
This provides an extra layer of assurance.

:::paragraph
Lean distributions include the following independently implemented kernels:

: Nanoda ({executable +def}`nanoda_bin`)

  An implementation of the Lean kernel in Rust by Chris Bailey ([source](https://github.com/ammkrn/nanoda_lib)).

: {executable +def}`lean4lean`

  A port of the official kernel to Lean by Mario Carneiro ([source](https://github.com/digama0/lean4lean)).
  Significant parts of it are formally verified against a specification of Lean's type theory.

: {executable +def}`con-leche`

  An implementation of the Lean kernel in Lean by the Lean FRO ([source](https://github.com/leanprover/con-leche)).
  It includes a machine-checked proof that every environment it accepts has a model in set theory, so it never accepts a proof of {name}`False`.

: {executable +def}`con-ron`

  A port of {executable}`con-leche` to Rust by the Lean FRO ([source](https://github.com/leanprover/con-ron)).

:::

Kernels do not need to be able to call any particular external API or use any particular data structures.
They are provided with a newline-delimited JSON file that contains all the terms and definitions to be checked.

# Lean Export Format
%%%
tag := "export-format"
%%%

This section describes version 3.1.0 of the export format.
The export is [newline-delimited JSON](https://github.com/ndjson/ndjson-spec): there is one object per line, and objects do not themselves contain newline characters.
An exported `.ndjson` file will begin with an {exportType "Initial metadata object"}[initial metadata object] which includes version info for the exporter, Lean, and export format:

```exportFormat "Initial metadata object"
{
  "meta": {
    "exporter": {
      "name": string,
      "version": string
    },
    "lean": {
      "githash": string,
      "version": string
    },
    "format": {
      "version": string
    }
  }
}
```

The metadata object is followed by a sequence of primitives with integer tags (Name, Level, or Expr) and declarations ({exportType "Axiom"}[axiom], {exportType "Definition"}[definition], {exportType "Theorem"}[theorem], {exportType "Opaque"}[opaque], {exportType "Quotient"}[quot], {exportType "Inductive Declaration"}[inductive] including {exportType "ConstructorVal"}[constructor] and {exportType "RecursorVal"}[recursor]), where related elements of an inductive or mutual inductive declaration (the inductive specifications, constructors, and recursors) are grouped together.

The export format contains information that is redundant and would likely be ignored or only validated by a full external checker (such as the types of recursors).
These are included for the benefit of other tools that want all constants with their types (e.g. dependency analysis tools).

The construction of these elements is as described below.
Line breaks are included for readability; note that the NDJSON format requires these JSON objects to be rendered without any line breaks.

## Indices

:::paragraph
The export format uses explicit indices to refer to names, levels, and expressions.
Each kind of object occupies its own table, and indices may be reused between tables.
Within a table, each index is unique.
The spec uses the following types to describe natural numbers that refer to entries in the table:

: {exportType +def}`NameIdx`

  An index into the name table, bound by {exportField}`in`.
  Index 0 refers to the anonymous name and is predefined.

: {exportType +def}`LevelIdx`

  An index into the {tech (key:="universe level")}[level] table, bound by {exportField}`il`.
  Index 0 refers to level 0 and is predefined.

: {exportType +def}`ExprIdx`

  An index into the expression table, bound by {exportField}`ie`.
  There are no predefined values.

: {exportType +def}`NameIdxDef`

  A {exportType}`NameIdx` defined by this line

: {exportType +def}`LevelIdxDef`

  A {exportType}`LevelIdx` defined by this line

: {exportType +def}`ExprIdxDef`

  A {exportType}`ExprIdx` defined by this line

If an index is defined more than once, the kernel should reject the code.
Every definition of an index must precede all uses; if an undefined index is encountered, the kernel should reject the code.
:::

Other integer fields represent integer values.
They may be de Bruijn indices ({exportField}`bvar`), numeric name components ({exportField}`i`), field indices ({exportField}`idx`), definition heights ({exportField}`regular`), constructor positions ({exportField}`cidx`), or counts ({exportField}`numParams`, {exportField}`numIndices`, {exportField}`numNested`, {exportField}`numFields`, {exportField}`numMotives`, {exportField}`numMinors`, {exportField}`nfields`).
Natural number literals are encoded as JSON string literals instead of JSON numbers to reduce the risk of parsers truncating values at limits such as $`2^{53}`.


## Names

Names have two formats that correspond to the constructors of {name}`Lean.Name`.
Index 0 is predefined to refer to {name}`Lean.Name.anonymous`.

```exportFormat "Name.str"
{
  "str": {
    "pre": NameIdx,
    "str": string
  },
  "in": NameIdxDef
}
```

```exportFormat "Name.num"
{
  "num": {
    "pre": NameIdx,
    "i": integer
  },
  "in": NameIdxDef
}
```

## Levels

{tech}[Universe levels] have four formats that correspond to the constructors of {name}`Lean.Level`.
Index 0 is predefined to refer to {name}`Lean.Level.zero` and is not otherwise represented.

```exportFormat "Level.succ"
{
  "succ": LevelIdx,
  "il": LevelIdxDef
}
```

```exportFormat "Level.max"
{
  "max": [LevelIdx, LevelIdx],
  "il": LevelIdxDef
}
```

```exportFormat "Level.imax"
{
  "imax": [LevelIdx, LevelIdx],
  "il": LevelIdxDef
}
```

```exportFormat "Level.param"
{
  "param": NameIdx,
  "il": LevelIdxDef
}
```

## Expressions

Each constructor of {name}`Lean.Expr` that may occur in elaborated code has a corresponding JSON representation.
Free variables and metavariables do not appear in the export.
There are no predefined expressions.

```exportFormat "Expr.bvar"
{
  "bvar": integer,
  "ie": ExprIdxDef
}
```


```exportFormat "Expr.sort"
{
  "sort": LevelIdx,
  "ie": ExprIdxDef
}
```

```exportFormat "Expr.const"
{
  "const": {
    "name": NameIdx,
    "us": Array<LevelIdx>
  },
  "ie": ExprIdxDef
}
```

```exportFormat "Expr.app"
{
  "app": {
    "fn": ExprIdx,
    "arg": ExprIdx
  },
  "ie": ExprIdxDef
}
```

```exportFormat "Expr.lam"
{
  "lam": {
    "name": NameIdx,
    "type": ExprIdx,
    "body": ExprIdx,
    "binderInfo": "default" | "implicit" | "strictImplicit" | "instImplicit"
  },
  "ie": ExprIdxDef
}
```

```exportFormat "Expr.forallE"
{
  "forallE": {
    "name": NameIdx,
    "type": ExprIdx,
    "body": ExprIdx,
    "binderInfo": "default" | "implicit" | "strictImplicit" | "instImplicit"
  },
  "ie": ExprIdxDef
}
```

```exportFormat "Expr.letE"
{
  "letE": {
    "name": NameIdx,
    "type": ExprIdx,
    "value": ExprIdx,
    "body": ExprIdx,
    "nondep": boolean
  },
  "ie": ExprIdxDef
}
```

```exportFormat "Expr.proj"
{
  "proj": {
    "typeName": NameIdx,
    "idx": integer,
    "struct": ExprIdx
  },
  "ie": ExprIdxDef
}
```

```exportFormat "Expr.lit (Literal.natVal)"
{
  "natVal": string,
  "ie": ExprIdxDef
}
```

```exportFormat "Expr.lit (Literal.strVal)"
{
  "strVal": string,
  "ie": ExprIdxDef
}
```

```exportFormat "Expr.mdata"
{
  "mdata": {
    "expr": ExprIdx,
    "data": object
  },
  "ie": ExprIdxDef
}
```

By default, metadata is stripped prior to export.
The `--export-mdata` flag causes it to be included; when they are present, {exportField}`data` is an object whose values are strings formatted by {name}`repr`.

## Declarations

Each kind of declaration in the core type theory has a corresponding JSON representation.
Sometimes, multiple kinds of Lean declarations elaborate to the same underlying representation; one example of this is {ref "structures"}[structures] and {ref "inductive-types"}[inductive types].
In this case, there is only a single representation.

### Axioms

```exportFormat "Axiom"
{
  "axiom": {
    "name": NameIdx,
    "levelParams": Array<NameIdx>,
    "type": ExprIdx,
    "isUnsafe": boolean
  }
}
```

### Definitions

```exportFormat "Definition"
{
  "def": {
    "name": NameIdx,
    "levelParams": Array<NameIdx>,
    "type": ExprIdx,
    "value": ExprIdx,
    "hints": "opaque" | "abbrev" | {"regular": integer},
    "safety": "unsafe" | "safe" | "partial",
    "all": Array<NameIdx>
  }
}
```

### Opaques

```exportFormat "Opaque"
{
  "opaque": {
    "name": NameIdx,
    "levelParams": Array<NameIdx>,
    "type": ExprIdx,
    "value": ExprIdx,
    "isUnsafe": boolean,
    "all": Array<NameIdx>
  }
}
```

### Theorems

```exportFormat "Theorem"
{
  "thm": {
    "name": NameIdx,
    "levelParams": Array<NameIdx>,
    "type": ExprIdx,
    "value": ExprIdx,
    "all": Array<NameIdx>
  }
}
```

### Quotients

The official Lean kernel uses the fieldless constructor {name}`Lean.Declaration.quotDecl` as the input to declare the quotient declarations.
It then adds the four declarations that make up the quotient package to the environment.
The export format includes the data of these generated declarations for convenience.

```exportFormat "Quotient"
{
  "quot": {
    "name": NameIdx,
    "levelParams": Array<NameIdx>,
    "type": ExprIdx,
    "kind": "type" | "ctor" | "lift" | "ind"
  }
}
```

### Inductive Declaration:

The official Lean kernel expects a {name}`Lean.Declaration.inductDecl`, which contains a (mutual) group of inductive declarations with their constructors.
From that the kernel derives the {tech}[recursors] and informational fields like {name Lean.InductiveVal.isRec}`isRec`, {name Lean.InductiveVal.isReflexive}`isReflexive` or {name Lean.ConstructorVal.cidx}`cidx`.
The export format includes the data of these generated declarations for convenience.
{tech}[ι-reductions] are specified by {exportType}`RecursorRule` entries.
Independent kernels may either trust the included derived recursor information or regenerate and check it for extra assurance.

```exportFormat "Inductive Declaration"
{
  "inductive": {
    "types": Array<InductiveVal>,
    "ctors": Array<ConstructorVal>,
    "recs": Array<RecursorVal>
  }
}
```

```exportFormat "InductiveVal"
{
  "name": NameIdx,
  "levelParams": Array<NameIdx>,
  "type": ExprIdx,
  "numParams": integer,
  "numIndices": integer,
  "all": Array<NameIdx>,
  "ctors": Array<NameIdx>,
  "numNested": integer,
  "isRec": boolean,
  "isUnsafe": boolean,
  "isReflexive": boolean
}
```

```exportFormat "ConstructorVal"
{
  "name": NameIdx,
  "levelParams": Array<NameIdx>,
  "type": ExprIdx,
  "induct": NameIdx,
  "cidx": integer,
  "numParams": integer,
  "numFields": integer,
  "isUnsafe": boolean
}
```

```exportFormat "RecursorVal"
{
  "name": NameIdx,
  "levelParams": Array<NameIdx>,
  "type": ExprIdx,
  "all": Array<NameIdx>,
  "numParams": integer,
  "numIndices": integer,
  "numMotives": integer,
  "numMinors": integer,
  "rules": Array<RecursorRule>,
  "k": boolean,
  "isUnsafe": boolean
}
```

```exportFormat "RecursorRule"
{
  "ctor": NameIdx,
  "nfields": integer,
  "rhs": ExprIdx
}
```
