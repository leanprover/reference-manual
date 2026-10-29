/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Wojciech Nawrocki
-/

import VersoManual
import Manual.Meta

import Lean.Data.Json

open Verso.Genre Manual InlineLean
open Lean

#doc (Manual) "JSON" =>
%%%
tag := "JSON"
%%%

The {name}`Json` datatype represents [JSON](https://www.json.org/json-en.html) values.
To use the type and related functionality, import {module}`Lean.Data.Json`.

{docstring +allowMissing Json}

JSON can express arbitrary precision rational numbers.
We store these as {name}`JsonNumber`s: a mantissa and a negative exponent.
Beware that if decoded in JavaScript, these numbers may [lose precision](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/JSON#lossless_number_serialization).

{docstring +allowMissing JsonNumber}

To parse JSON text into a {name}`Json` value, use {name}`Json.parse`.
Note that {name}`Json.parse` is not necessarily robust against adversarial inputs.
For example, objects with duplicate keys (`{ "a": 1, "a": 2 }`) have unspecified decodings.

{docstring +allowMissing Json.parse}

In the other direction, there are two ways to render {name}`Json` values as text.
To optimize for compact representation, invoke {name}`Json.compress`.
Alternatively, to produce human-readable output, call {name}`Json.render` or {name}`Json.pretty`.

{docstring +allowMissing Json.compress}

{docstring +allowMissing Json.render}

{docstring +allowMissing Json.pretty}

# Literal Syntax

In addition to using the {name}`Json` constructors directly, JSON values can be written in standard notation following the `json%` keyword.

:::syntax term (title := "JSON Terms")
```grammar
json% $_:json
```
:::

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

The complete grammar of JSON literals is as follows.

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

# Serialization

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

Many helper functions are available for writing custom JSON encoders and decoders.

For creating JSON values, we have among others {name}`Json.mkObj`, {name}`Json.setObjVal!`, and {name}`Json.setObjValAs!`.

For decoding JSON, the following can be useful: {name}`Json.isNull`, {name}`Json.getStr?`, {name}`Json.getNat?`, {name}`Json.getInt?`, {name}`Json.getBool?`,  {name}`Json.getArr?`, {name}`Json.getArrVal?`, {name}`Json.getObjVal?`, {name}`Json.getObjValD`, {name}`Json.getObjValAs?`.
