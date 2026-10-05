/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Wojciech Nawrocki
-/

import VersoManual
import Manual.Meta

import Lean.Data.Html

set_option pp.rawOnError true

open Verso.Genre Manual InlineLean
open Lean Parser Html

#doc (Manual) "Web Technologies" =>
%%%
tag := "web-technologies"
%%%

The Lean distribution includes support for certain web technologies:
there are data types and DSL syntax for authoring HTML content,
as well as for working with JSON representations of data.
In graphical development environments,
the widget system makes it possible to extend the infoview
(the editor panel that shows tactic states, messages, and other information relevant to the current cursor position)
with new React components.
Widgets can execute Lean code in the LSP server via remote procedure calls (RPC).

# JSON

The {name}`Json` datatype represents [JSON](https://www.json.org/json-en.html) values.
To use it, import {module}`Lean.Data.Json.Basic`.

{docstring +allowMissing Json}

The modules {module}`Lean.Data.Json.Parser` and {module}`Lean.Data.Json.Printer`
provide functions to parse and render JSON values from/to strings, respectively.

{docstring +allowMissing Json.parse}

There are two renderers: {name}`Json.render` and {name}`Json.pretty` produce human-readable output,
whereas {name}`Json.compress` optimizes for compact representation.

{docstring +allowMissing Json.render}

{docstring +allowMissing Json.pretty}

{docstring +allowMissing Json.compress}

## Literal Syntax

In addition to using the {name}`Json` constructors directly,
JSON values can be written in standard notation following the `json%` keyword.
This syntax extension is defined in {module}`Lean.Data.Json.Elab`.

:::syntax term (title := "JSON Terms")
```grammar
json% $_:json
```
:::

:::comment
Using `freeSyntax` because `syntax` can't render multiple productions in one BNF.
:::
:::freeSyntax json (title := "JSON Literals") -open
```grammar
`( json|null)
*****
`( json|true)
*****
`( json|false)
*****
`( json|$_:str)
*****
`( json|$[-]? $_:num)
*****
`( json|$[-]? $_:scientific)
*****
`( json|[ $[$_:json],* ])
*****
`( json|{ $[$k:jsonIdent : $v:json],* })
```
:::

:::freeSyntax Lean.Json.jsonIdent (title := "JSON Field Names") -open
```grammar
`(Lean.Json.jsonIdent| $_:ident)
*****
`(Lean.Json.jsonIdent| $_:str)
```
:::

:::leanSection
```lean -show
variable { j : Json }
```
The literal syntax supports antiquotation of JSON values.
For example, given {typed}`j : Json` we may write {lean}`json% { field: $(j) }`.
:::

## Serialization

Serialization of Lean values to JSON, and deserialization from JSON,
is supported through the {name}`ToJson` and {name}`FromJson` typeclasses.
Import {module}`Lean.Data.Json.FromToJson` to use this functionality.

JSON representations of many Lean types can be derived automatically.
The default encoding is documented on {name}`ToJson` (below).

:::example "Serializing a structure to JSON"
```imports -show
import Lean.Data.Json.FromToJson
```
```lean -show
open Lean

```
```lean (name := fooJson)
structure Foo where
  x : Bool := true
  y : String := "abc"
  z? : Option Nat := some 1
  deriving ToJson, FromJson

#eval toJson { : Foo }
```
```leanOutput fooJson +show
{"z": 1, "y": "abc", "x": true}
```
:::

{docstring +allowMissing ToJson}

{docstring +allowMissing FromJson}

# HTML

The {name}`Html` type represents HTML content.
It is accessed by importing {module}`Lean.Data.Html.Basic`.

{docstring Html}

This inductive type has a degree of redundancy:
{lean}`Html.seq #[]` and {lean}`Html.seq #[Html.seq #[]]`, for instance,
denote the same, empty piece of HTML.
Functions in the library generally normalize their {name}`Html` outputs,
while accepting non-normal inputs.
The {name}`Html.isEmpty` recognizer, for example, handles non-normal values.

{docstring Html.ofArray}

{docstring Html.isEmpty}

The {name}`render` function, defined in the {module}`Lean.Data.Html.Printer` module,
turns {ref "inductive-types"}`inductively` represented HTML
into a string that can be parsed by browsers.

{docstring render}

## Literal Syntax

A grammar for HTML is defined in {module}`Lean.Data.Html.Syntax`.
It does not declare any {ref "syntax-categories"}`syntax category`,
instead consisting entirely of {name}`Parser`s
(see the source module for a justification).
The top-level parser is {name}`Syntax.content`.

{docstring Syntax.content}

The syntactic category of Lean terms includes HTML literals via the `html${}` delimiter.
These literals {ref "elaborators"}`elaborate` to {name}`Html` values.

:::syntax term (title := "HTML Literals")
```grammar
html%{$html:content}
```
:::

The following parsers,
invoked recursively by {name}`Syntax.content` and each other,
cover the supported kinds of HTML syntax.

{docstring Syntax.text}

{docstring Syntax.comment}

{docstring Syntax.element}

{docstring Syntax.tagName}

{docstring Syntax.attr}

{docstring Syntax.attrName}

:::leanSection
```lean -show
variable {html : Html} {htmls : Array Html} {attr : String × String} {attrs : Array (String × String)} {val : String}
```
_Interpolations_ are holes in the syntax, filled in with a Lean term of the correct type.
They are written with curly braces and supported in:

- _Content._ Given one value {typed}`html : Html` or multiple {typed}`htmls : Array Html` (or any collection),
  we can write {lean}`html%{<tag>{html} {...htmls}</tag>}`.
- _Attributes._ Given one value {typed}`attr : String × String` or multiple {typed}`attrs : Array (String × String)` (or any collection),
  we can write {lean}`html%{<tag {attr} {...attrs} />}`.
- _Attribute values._ Given {typed}`val : String`,
  we can write {lean}`html%{<tag attr-name={val} />}`.
:::

### Custom elaborators

The HTML syntax is designed to support elaboration into custom types besides the {name}`Html` type.
This is facilitated by _view_ functions that provide convenient descriptions of the parsed syntax.
For instance, the {name}`Syntax.Content.view` function describes a {name}`Syntax.Content` node —
an alias for {lean}`TSyntax Syntax.contentKind` —
as a sequence of items.

:::sectionNote
The builtin elaborator in {module}`Lean.Data.Html.Elab` is a useful reference for how to use views.
:::

{docstring Syntax.Content.view}

{docstring +allowMissing Syntax.ContentItemView}

Views are lazy, with one level of depth: a view describes the current syntax node,
but the arguments to its constructors are again ordinary Lean {name}`Syntax`.
For instance, the argument to {name}`Syntax.ContentItemView.element` is {name}`Syntax.Element`,
an alias for {lean}`TSyntax Syntax.elementKind`.
An elaborator based on views invokes view functions
whenever it needs to inspect a further piece of syntax.

### Adherence to WhatWG Specification

The HTML syntax is optimized for authoring HTML content within Lean,
rather than parsing existing HTML documents.
As such, is not guaranteed to comply with the [WhatWG specification](https://html.spec.whatwg.org/multipage/syntax.html).
That said, it tries to match the specification in most cases;
known departures from the specification are documented on the relevant parser.

# Widgets

:::TODO
:::

## Remote Procedure Calls

:::TODO
:::
