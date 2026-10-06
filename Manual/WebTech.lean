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

The Lean distribution includes support for certain web technologies: there are data types and DSL syntax for authoring HTML content, as well as for working with JSON representations of data.
In graphical development environments, the widget system makes it possible to extend the InfoView (the editor panel that shows tactic states, messages, and other information relevant to the current cursor position) with new React components.
Widgets can execute Lean code in the LSP server via remote procedure calls (RPC).

# JSON

The {name}`Json` datatype represents [JSON](https://www.json.org/json-en.html) values.
To use the type and related functionality, import {module}`Lean.Data.Json`.

{docstring +allowMissing Json}

JSON can express arbitrary precision rational numbers.
We store these as {name}`JsonNumber`s: a mantissa and a negative exponent.
Beware that if decoded in JavaScript, these numbers may [lose precision](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/JSON#lossless_number_serialization).

{docstring +allowMissing JsonNumber}

To parse JSON text into a {name}`Json` value, use {name}`Json.parse`.

{docstring +allowMissing Json.parse}

In the other direction, there are two ways to render {name}`Json` values as text.
To optimize for compact representation, invoke {name}`Json.compress`.
Alternatively, to produce human-readable output, call {name}`Json.render` or {name}`Json.pretty`.

{docstring +allowMissing Json.compress}

{docstring +allowMissing Json.render}

{docstring +allowMissing Json.pretty}

## Literal Syntax

In addition to using the {name}`Json` constructors directly, JSON values can be written in standard notation following the `json%` keyword.

One may optionally omit quotes on object keys in `json%` literals (similarly to [JavaScript object literals](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Guide/Working_with_objects#using_object_initializers)).
A `$()` delimiter can be used to interpolate any value with a {name}`FromJson` instance (including {name}`Json` values).

:::example "Using a JSON literal"
```imports -show
import Lean.Data.Json
```
```lean -show
open Lean
```
```lean
variable (j : Json)

#check json% {
  "a": 1,
  "b": [2, 3],
  c: null,
  d: $(j)
}
```
:::

:::syntax term (title := "JSON Terms")
```grammar
json% $_:json
```
:::

:::comment
Using `freeSyntax` due to https://github.com/leanprover/reference-manual/issues/966.
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
`( json|{ $[$_:jsonIdent : $_:json],* })
*****
"$("$_:term")"
```
:::

:::freeSyntax Lean.Json.jsonIdent (title := "JSON Field Names") -open
```grammar
`(Lean.Json.jsonIdent| $_:ident)
*****
`(Lean.Json.jsonIdent| $_:str)
```
:::

## Serialization

Serialization of Lean values to JSON, and deserialization from JSON, is supported through the {name}`ToJson` and {name}`FromJson` typeclasses.
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

This inductive type has a degree of redundancy: {lean}`Html.seq #[]` and {lean}`Html.seq #[Html.seq #[]]`, for example, denote the same, empty piece of HTML.
Functions in the library generally normalize their {name}`Html` outputs, while accepting non-normal inputs.
Recognizers such as {name}`Html.isEmpty` handle non-normal values.

{docstring Html.ofArray}

{docstring Html.isEmpty}

The {name}`render` function, defined in the {module}`Lean.Data.Html.Printer` module, turns {ref "inductive-types"}[inductively] represented HTML into a string that can be parsed by browsers.

{docstring render}

## Literal Syntax

A grammar for HTML is defined in {module}`Lean.Data.Html.Syntax`.
It does not declare any {ref "syntax-categories"}[syntax category], instead consisting entirely of {name}`Parser`s (see the source module for a justification).
The top-level parser is {name}`Syntax.content`.

:::TODO
document whitespace rules
:::

{docstring Syntax.content}

The syntactic category of Lean terms includes HTML literals via the `html%{}` delimiter.
These literals {ref "elaborators"}[elaborate] to {name}`Html` values.

:::syntax term (title := "HTML Literals")
```grammar
html%{$html:content}
```
:::

The following parsers, invoked recursively by {name}`Syntax.content` and each other, cover the supported kinds of HTML syntax.

{docstring Syntax.text}

{docstring Syntax.comment}

{docstring Syntax.element}

{docstring Syntax.tagName}

{docstring Syntax.attr}

{docstring Syntax.attrName}

:::leanSection
```lean -show
variable {html : Html} {htmls : Array Html}
  {ρ : Type} [ForIn Id ρ Html] {htmls' : ρ}
  {attr : String × String} {attrs : Array (String × String)}
  {σ : Type} [ForIn Id σ (String × String)] {attrs' : σ}
  {val : String}
```
_Interpolations_ are holes in the syntax, filled in with a Lean term of the correct type.
They are written with curly braces and supported in:

: Content

  - Given an {typed}`html : Html` value, we can write {lean}`html%{<tag>{html}</tag>}`.
  - Given multiple values {typed}`htmls : Array Html`, or more generally any collection {typed}`htmls' : ρ` with a {lean}`ForIn Id ρ Html` instance, we can write {lean}`html%{<tag>{...htmls}{...htmls'}</tag>}`.

: Attributes

  - Given an {typed}`attr : String × String` value, we can write {lean}`html%{<tag {attr} />}`.
  - Given multiple values {typed}`attrs : Array (String × String)`, or more generally any collection {typed}`attrs' : σ` with a {lean}`ForIn Id σ (String × String)` instance, we can write {lean}`html%{<tag {...attrs} {...attrs'} />}`.

: Attribute values

  Given {typed}`val : String`, we can write {lean}`html%{<tag attr-name={val} />}`.
:::

### Custom elaborators

The HTML syntax is designed to support elaboration into custom types besides the {name}`Html` type.
This is facilitated by _view_ functions that provide convenient descriptions of the parsed syntax.
For instance, the {name}`Syntax.Content.view` function describes a {name}`Syntax.Content` node—an alias for {lean}`TSyntax Syntax.contentKind`—as a sequence of items.

:::sectionNote
The `html%{}` literal elaborator in {module}`Lean.Data.Html.Elab` is a useful example of how to use views.
:::

{docstring Syntax.Content.view}

{docstring +allowMissing Syntax.ContentItemView}

Views are lazy, with one level of depth: a view describes the current syntax node, but the arguments to its constructors are again ordinary {name}`Lean.TSyntax`.
For instance, the argument to {name}`Syntax.ContentItemView.element` is {name}`Syntax.Element`, an alias for {lean}`TSyntax Syntax.elementKind`.
An elaborator based on views invokes view functions whenever it needs to inspect a further piece of syntax.

### Adherence to WhatWG Specification

The HTML syntax is optimized for authoring HTML content within Lean, rather than parsing existing HTML documents.
As such, is not guaranteed to comply with the [WhatWG specification](https://html.spec.whatwg.org/multipage/syntax.html).
That said, it tries to match the specification in most cases; known departures from the specification are documented on the relevant parser.

# Widgets

:::TODO
:::

## Remote Procedure Calls

:::TODO
:::
