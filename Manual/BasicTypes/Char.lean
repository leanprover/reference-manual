/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Manual.BasicTypes.Array.Subarray
import Manual.BasicTypes.Array.FFI

open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Characters" =>
%%%
tag := "Char"
%%%

Characters are represented by the type {name}`Char`, which may be any Unicode [scalar value](http://www.unicode.org/glossary/#unicode_scalar_value).
While {ref "String"}[strings] are UTF-8-encoded arrays of bytes, characters are represented by full 32-bit values.
Lean provides special {ref "char-syntax"}[syntax] for character literals.

# Logical Model
%%%
tag := "char-model"
%%%

From the perspective of Lean's logic, characters consist of a 32-bit unsigned integer paired with a proof that it is a valid Unicode scalar value.

{docstring Char}

# Run-Time Representation
%%%
tag := "char-runtime"
%%%

As a {ref "inductive-types-trivial-wrappers"}[trivial wrapper], characters are represented identically to {lean}`UInt32`.
In particular, characters are represented as 32-bit immediate values in monomorphic contexts.
In other words, a field of a constructor or structure of type {lean}`Char` does not require indirection to access.
In polymorphic contexts, characters are {tech}[boxed].


# Syntax
%%%
tag := "char-syntax"
%%%

Character literals consist of a single character or an escape sequence enclosed in single quotes (`'`, Unicode `'APOSTROPHE' (U+0027)`).
Between these single quotes, the character literal may contain character other that `'`, including newlines, which are included literally (with the caveat that all newlines in a Lean source file are interpreted as `'\n'`, regardless of file encoding and platform).
Special characters may be escaped with a backslash, so `'\''` is a character literal that contains a single quote.
The following forms of escape sequences are accepted:

: `\r`, `\n`, `\t`, `\\`, `\"`, `\'`

  These escape sequences have the usual meaning, mapping to `CR`, `LF`, tab, backslash, double quote, and single quote, respectively.

: `\xNN`

  When `NN` is a sequence of two hexadecimal digits, this escape denotes the character whose Unicode code point is indicated by the two-digit hexadecimal code.

: `\uNNNN`

  When `NN` is a sequence of two hexadecimal digits, this escape denotes the character whose Unicode code point is indicated by the four-digit hexadecimal code.


# API Reference
%%%
tag := "char-api"
%%%

## Conversions

{docstring Char.ofNat}

{docstring Char.toNat}

{docstring Char.isValidCharNat}

{docstring Char.ofUInt8}

{docstring Char.toUInt8}


There are two ways to convert a character to a string.
{name}`Char.toString` converts a character to a singleton string that consists of only that character, while {name}`Char.quote` converts the character to a string representation of the corresponding character literal.

{docstring Char.toString}

{docstring Char.quote}

:::example "From Characters to Strings"

{name}`Char.toString` produces a string that contains only the character in question:

```lean (name := e)
#eval 'e'.toString
```
```leanOutput e
"e"
```

```lean (name := e')
#eval '\x65'.toString
```
```leanOutput e'
"e"
```

```lean (name := n')
#eval '"'.toString
```
```leanOutput n'
"\""
```

{name}`Char.quote` produces a string that contains a character literal, suitably escaped:
```lean (name := eq)
#eval 'e'.quote
```
```leanOutput eq
"'e'"
```

```lean (name := eq')
#eval '\x65'.quote
```
```leanOutput eq'
"'e'"
```

```lean (name := nq')
#eval '"'.quote
```
```leanOutput nq'
"'\\\"'"
```


:::




## Character Classes
%%%
tag := "char-api-classes"
%%%

{docstring Char.isAlpha}

{docstring Char.isAlphanum}

{docstring Char.isDigit}

{docstring Char.isLower}

{docstring Char.isUpper}

{docstring Char.isWhitespace}

## Case Conversion

{docstring Char.toUpper}

{docstring Char.toLower}

## Comparisons

{docstring Char.le}

{docstring Char.lt}

## Unicode

{docstring Char.utf8Size}

{docstring Char.utf16Size}
