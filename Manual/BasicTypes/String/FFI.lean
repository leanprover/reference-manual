/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
open Manual.FFIDocType

open Verso.Genre Manual

set_option pp.rawOnError true


#doc (Manual) "FFI" =>
%%%
tag := "string-ffi"
%%%


{docstring String.csize}

:::ffi "lean_string_object" kind := type
```
typedef struct {
    lean_object m_header;
    /* byte length including '\0' terminator */
    size_t      m_size;
    size_t      m_capacity;
    /* UTF8 length */
    size_t      m_length;
    char        m_data[0];
} lean_string_object;
```
The representation of strings in C. See {ref "string-runtime"}[the description of run-time {name}`String`s] for more details.
:::

:::ffi "lean_is_string"
````
bool lean_is_string(lean_object * o)
````

Returns `true` if `o` is a string, or `false` otherwise.
:::

:::ffi "lean_to_string"
````
lean_string_object * lean_to_string(lean_object * o)
````
Performs a runtime check that `o` is indeed a string. If `o` is not a string, an assertion fails.
:::

:::planned 158
 * Complete C API for {lean}`String`
:::
