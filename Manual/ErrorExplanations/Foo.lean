import VersoManual
import Manual.Meta.ErrorExplanation

open Lean
open Verso.Genre Manual InlineLean

#doc (Manual) "About: `foo`" =>
%%%
shortTitle := "foo"
%%%

{errorExplanationHeader lean.foo}

...mandatory short description...

# Examples
:::errorExample "Headline Cased Description"
```broken
example := x
```
```output
Unknown identifier `x`
```
```fixed
def x := 19
example := x
```

...optional short discussion of example...
:::
