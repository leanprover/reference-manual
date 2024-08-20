import VersoManual

import Manual.Meta
open Manual.FFIDocType

open Verso.Genre Manual

set_option pp.rawOnError true


#doc (Manual) "Logical Model" =>

{docstring String}

The logical model of strings in Lean is a structure that contains a single field, which is a list of characters.
This is convenient when specifying and proving properties of string-processing fuctions at a low level.
