/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta

import Lean.Parser.Command

open Manual
open Verso.Genre
open Verso.Genre.Manual

set_option pp.rawOnError true

set_option linter.unusedVariables false

#doc (Manual) "Console Output" =>

Lean includes convenience functions for writing to {tech}[standard output] and {tech}[standard error].
All make use of {lean}`ToString` instances, and the varieties whose names end in `-ln` add a newline after the output.
These convenience functions only expose a part of the functionality available {ref "stdio"}[using the standard I/O streams].
In particular, to read a line from standard input, use a combination of {lean}`IO.getStdin` and {lean}`IO.FS.Stream.getLine`.

{docstring IO.print}

{docstring IO.println}

{docstring IO.eprint}

{docstring IO.eprintln}

::::example "Printing"
This program demonstrates all four convenience functions for console I/O.

:::ioExample
```ioLean
def main : IO Unit := do
  IO.print "This is the "
  IO.print "Lean"
  IO.println " language reference."
  IO.println "Thank you for reading it!"
  IO.eprint "Please report any "
  IO.eprint "errors"
  IO.eprintln " so they can be corrected."
```

It outputs the following to the standard output:

```stdout
This is the Lean language reference.
Thank you for reading it!
```

and the following to the standard error:

```stderr
Please report any errors so they can be corrected.
```
:::
::::
