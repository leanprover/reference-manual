# Writing Error Explanations

Error explanations give more context and discussion than is reasonable to
include in an actual error message. The error message in the Lean InfoView
contains a link to the error explanation for further reading.

An error explanation is just a manual page obeying a few conventions:
 * Defined in the module `Manual.ErrorExplanations.ErrorSuffix`
 * Titled `About: `{errorSuffix}`"
 * Has the `shortTitle` property `"errorSuffix"`
 * Starts with a `{errorExplanationHeader lean.errorSuffix}` block command
 * Contains a single section header, `Examples`, and that section contains
   only a series of `errorExample` directives
 * Included in alphabetical order in the `Manual.ErrorExplanations` module

For the `lean.ctorResultingTypeMismatch` named error, `errorSuffix` is
`ctorResultingTypeMismatch` and `ErrorSuffix` is `CtorResultingTypeMismatch`.
The reference manual should only need to contain docs for `lean.*` error
names.

Failing to include an error explanation for an error defined in the
toolchain's Lean version will cause an error when generating the manual.
Including an error explanation that isn't yet in the toolchain's Lean version
only generates a warning. This makes it simpler to write write error
explanations for newly-added errors.

### Example

For a new named error `lean.foo`, the `Manual.ErrorExplanations` module
will need to import `Manual.ErrorExplanations.Foo` and include the line 
`{include 0 Manual.ErrorExplanations.Foo}`. 

```
/- Manual/ErrorExplanations/Foo.lean -/

import VersoManual
import Manual.Meta.ErrorExplanation

open Lean Doc
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