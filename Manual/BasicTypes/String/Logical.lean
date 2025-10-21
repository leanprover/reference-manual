/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
open Manual.FFIDocType

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true


#doc (Manual) "Logical Model" =>

{docstring String}

:::paragraph
The logical model of strings in Lean is a structure that contains two fields:

 * {name}`String.bytes` is a {name}`ByteArray`, which contains the UTF-8 encoding of the string.

 * {name}`String.isValidUTF8` is a proof that the bytes are in fact a valid UTF-8 encoding of a string.

This model allows operations on byte arrays to be used to specify and prove properties about string operations at a low level while still building on the theory of byte arrays.
At the same time, it is close enough to the real run-time representation to avoid impedance mismatches between the logical model and the operations that make sense in the run-time representation.
:::

# Backwards Compatibility

In prior versions of Lean, the logical model of strings was a structure that contained a list of characters.
This model is accessible using {name}`String.mk`, which converts a list of characters into a {name}`String`, and {name}`String.data`, which converts a {name}`String` into a list of characters.
Their names reflect their prior status as the constructor of and projection from the logical model of strings.

{docstring String.mk}

{docstring String.data +allowMissing}
