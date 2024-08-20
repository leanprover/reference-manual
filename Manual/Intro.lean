import VersoManual

import Manual.Meta

open Lean.MessageSeverity

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Introduction" =>

This document describes version {versionString}[] of Lean.

The Lean language reference is intended as a comprehensive, precise description of Lean.


# Typographical Conventions

Lean code examples:

````lean
def hello : IO Unit := IO.println "Hello, world!"
````

Compiler output (which may be errors, warnings, or just information) is shown both in the code and separately:

````lean (name := output) (error := true)
#eval s!"The answer is {2 + 2}"

theorem bogus : False := by sorry

example := Nat.succ "two"
````

```leanOutput output (severity := information)
"The answer is 4"
```
```leanOutput output (severity := warning)
declaration uses 'sorry'
```
```leanOutput output (severity := error)
application type mismatch
  Nat.succ "two"
argument
  "two"
has type
  String : Type
but is expected to have type
  Nat : Type
```
