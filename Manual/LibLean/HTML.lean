/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Wojciech Nawrocki
-/

import VersoManual
import Manual.Meta

import Lean.Data.Html

open Verso.Genre Manual InlineLean
open Lean Parser Html

#doc (Manual) "HTML" =>
%%%
tag := "HTML"
%%%

The {name}`Html` type represents HTML content.
It is accessed by importing {module}`Lean.Data.Html.Basic`.

{docstring Html}

Because this inductive type includes a sequence constructor, its values are multi-rooted HTML _forests_ rather than single-rooted trees.
This is convenient for grouping content, as in {lean}`Html.seq #[.text "Paragraph.", .element "br" #[] .empty]`, but also introduces redundancy.
The empty HTML forest, for example, is denoted by {lean}`Html.seq #[]`, by {lean}`Html.seq #[Html.seq #[]]`, and by infinitely many other expressions.
To counter this, {name}`Html.isEmpty` recognizes any input that renders to the empty string, not just the simplest one.
In general, functions that consume {name}`Html` should handle all possible forms of their input.

{docstring Html.isEmpty}

Furthermore, to improve representation efficiency, functions that produce {name}`Html` may simplify it on a best-effort basis.
For example, {name}`Html.append` merges {name}`Html.seq` nodes.

{docstring Html.append}

Smart constructors such as {name}`Html.ofCollection`, {name}`Html.ofArray`, and {name}`Html.ofList` also simplify in this way, so should be preferred over {name}`Html.seq`.

{docstring Html.ofCollection}

{docstring Html.ofArray}

{docstring Html.ofList}

# Rendering

The {name}`render` function, defined in the {module}`Lean.Data.Html.Printer` module, turns HTML values into strings that can be parsed by browsers.

{docstring render}

# Literal Syntax

HTML literal notation can be accessed by importing {module}`Lean.Data.Html`.
These literals are written inside `html%{}` delimiters, and {ref "elaborators"}[elaborate] to {name}`Html` values.

:::syntax term (title := "HTML Terms")
```grammar
html%{$html:content}
```
:::

:::example "An HTML literal"
```imports -show
import Lean.Data.Html
```
```lean
#check html%{Hello, <b>world</b>!}
```
:::

HTML content is a sequence of zero or more content items.

:::comment
`attr*` below gets parsed as an attribute name, so the hover is wrong.
:::
:::freeSyntax contentItem (title := "HTML Content Item") -open
```grammar
$_:text
*****
`(Lean.Html.Syntax.comment|<!-- comment -->)
*****
`(Lean.Html.Syntax.element|<tagName attr*>$_:content</tagName>)
*****
`(Lean.Html.Syntax.element|<tagName attr*/>)
*****
"{"$_:term"}"
*****
"{..."$_:term"}"
```
:::

:::freeSyntax Lean.Html.Syntax.attr (title := "HTML Attribute") -open
```grammar
`(Lean.Html.Syntax.attr|attrName=$_:str)
*****
`(Lean.Html.Syntax.attr|attrName={$_:term})
*****
`(Lean.Html.Syntax.attr|attrName )
*****
`(Lean.Html.Syntax.attr|{$_:term})
*****
`(Lean.Html.Syntax.attr|{... $_:term})
```
:::

:::leanSection
```lean -show
variable {html : Html} {htmls : Array Html}
  {ρ : Type} [ForIn Id ρ Html] {htmls' : ρ}
  {attr : String × String} {attrs : Array (String × String)}
  {σ : Type} [ForIn Id σ (String × String)] {attrs' : σ}
  {val : String}
```

Besides standard HTML features, the grammar above includes {deftech (key := "html-interpolation")}[interpolations] written with curly braces.
These are holes in the syntax, filled in with a Lean term of the correct type (cf. {ref "string-interpolation"}[string interpolation]).
They are supported in:

: Content

  - Given an {typed}`html : Html` value, we can write {lean}`html%{<tag>{html}</tag>}`.
  - Given multiple values {typed}`htmls : Array Html`, or more generally any collection {typed}`htmls' : ρ` with a {lean}`ForIn Id ρ Html` instance, we can write {lean}`html%{<tag>{...htmls}{...htmls'}</tag>}`.

: Attributes

  - Given an {typed}`attr : String × String` value, we can write {lean}`html%{<tag {attr} />}`.
  - Given multiple values {typed}`attrs : Array (String × String)`, or more generally any collection {typed}`attrs' : σ` with a {lean}`ForIn Id σ (String × String)` instance, we can write {lean}`html%{<tag {...attrs} {...attrs'} />}`.

: Attribute values

  Given {typed}`val : String`, we can write {lean}`html%{<tag attr-name={val} />}`.
:::

[HTML character references](https://html.spec.whatwg.org/dev/syntax.html#character-references) in text and in double-quoted attribute values are decoded to the Unicode characters they represent.

:::example "Character reference in HTML literal"
```imports -show
import Lean.Data.Html
```
```lean
#check html%{&lt;}
```
:::

Whitespace in HTML content is governed by the following rules:
- Whitespace that contains a newline (U+000A or U+000D), and is not surrounded by text on both sides, is removed.
- Other consecutive whitespace is collapsed into a single space (U+0020).

:::example "Whitespace in HTML literal"
```imports -show
import Lean.Data.Html
```
```lean
#check html%{
  <ul>
    <li>Item  1</li>
    <li>Item
    2</li>
    <li>Item <b>3</b></li>
  </ul>
}
```
:::

## Custom elaborators

The HTML syntax is designed to support elaboration into custom types besides the {name}`Html` type.
It is implemented in {module}`Lean.Data.Html.Syntax` as a collection of {name}`Parser`s.
The top-level parser is {name}`Syntax.content`.
No {ref "syntax-categories"}[syntax category] is declared.

Elaboration is facilitated by _view_ functions that provide convenient descriptions of the parsed syntax.
For instance, the {name}`Syntax.Content.view` function describes a {name}`Syntax.Content` node as a sequence of items.
({name}`Syntax.Content` is an alias for {lean}`TSyntax Syntax.contentKind`.)

:::sectionNote
The `html%{}` literal elaborator in {module}`Lean.Data.Html.Elab` is a useful example of how to use views.
:::

{docstring Syntax.Content.view}

{docstring +allowMissing Syntax.ContentItemView}

Views implement details of whitespace handling and character reference decoding, simplifying elaborator implementations.

They operate at one level of depth: a view describes the current syntax node, but the arguments to its constructors are again ordinary {name}`Lean.TSyntax`, as opposed to being themselves described by nested views.
For instance, the argument to {name}`Syntax.ContentItemView.element` is {name}`Syntax.Element` (an alias for {lean}`TSyntax Syntax.elementKind`), not {name}`Syntax.ElementView`.
An elaborator based on views progressively invokes view functions whenever it needs to inspect more syntax.

## Adherence to WhatWG Specification

The HTML syntax is optimized for authoring HTML content within Lean, rather than parsing existing HTML documents.
As such, is not guaranteed to comply with the [WhatWG specification](https://html.spec.whatwg.org/multipage/syntax.html).
That said, it tries to match the specification in most cases; known departures from the specification are documented on the relevant parser.
