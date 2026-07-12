# Writing Error Explanations

Error explanations give more context and discussion than is reasonable
to include in an actual error message. The error message in the Lean
InfoView contains a link to the error explanation for further reading.

An error explanation is just a manual page obeying a few conventions:

- Defined in the module `Manual.ErrorExplanations.{ErrorSuffix}`
- Titled ``About: `{errorSuffix}`"``
- Has the `shortTitle` property `"{errorSuffix}"`
- Starts with a `{errorExplanationHeader lean.{errorSuffix}}` block
  command
- A description
- Contains a single section header, `Examples`, and that section
  contains only a series of `errorExample` directives
- Included in alphabetical order in the `Manual.ErrorExplanations`
  module

For the `lean.ctorResultingTypeMismatch` named error, `{errorSuffix}`
is `ctorResultingTypeMismatch` and `{ErrorSuffix}` is
`CtorResultingTypeMismatch`. The reference manual should only need to
contain docs for `lean.*` error names.

## Error Explanations in the Compiler

New error explanations are declared with the
`register_error_explanation` command and take a
`Lean.ErrorExplanation.Metadata` structure describing the error. All
errors have two-component names: the first identifies the package or
"domain" to which the error belongs (in core, this will always be
`lean`); the second identifies the error itself. Error names are
written in camel case and should be descriptive but not excessively
verbose. Abbreviations in error names are acceptable, but they should
be reasonably clear (e.g., abbreviations that are commonly used
elsewhere in Lean, such as `Ctor` for "constructor") and should not be
ambiguous with other vocabulary likely to appear in error names (e.g.,
use `Indep` rather than `Ind` for "independent," since the latter
could be confused with "inductive").

You can write an error explanation for a named error that hasn't been
registered yet; this will only generate a warning when building the
reference manual. You shouldn't merge a new registered error name
until the reference manual contains an error explanation.

Failing to include an error explanation for an error defined in the
toolchain's Lean version will cause an error when generating the
manual.

## Descriptions

The description should begin by explaining the meaning of the error
and why it occurs. It should also briefly explain, if appropriate, any
relevant context, such as related errors or relevant entries in the
reference manual. The latter is especially useful for directing users
to important concepts for understanding an error: while it is
appropriate to provide brief conceptual exposition in an error
explanation, avoid extensively duplicating content that can be found
elsewhere in the manual. General resolution or debugging strategies
not tied to specific examples can also be discussed in the description
portion of an explanation.

## Examples

The second half of an explanation (set off by the level-1 header
"Examples") contains annotated code examples. Each contains a `broken`
code block containing a self-contained minimal working (or
error-producing) examples (MWEs), followed by an `output` code block
containing the error. Subsequent code blocks should be labeled `fixed`
and should illustrate how to rewrite the code correctly. (If there is
more than one, they require a title given as a positional string
argument.) Finally, after these MWEs, include explanatory text
describing the example and the cause and resolution of the error it
demonstrates.

Note that each MWE in an example will be rendered as a tab, and the
full example (including its explanatory text) will appear in a
collapsible "Example" block like those used elsewhere in the manual.
Examples should center on code: prose not specific to the example
should generally appear in the initial half of the explanation.
However, an example should provide sufficient commentary for users to
understand how it illustrates relevant ideas from the preceding
description and what was done to resolve the exemplified error.

Choose examples carefully: they should be relatively minimal, so as to
draw out the error itself, but not so contrived as to impede
comprehension. Each should contain a distinct, representative instance
of the error to avoid the need for excessively many.

## Example Error Explanation

For a new named error `lean.foo`, the `Manual.ErrorExplanations`
module will need to import `Manual.ErrorExplanations.Foo` and include
the line `{include 0 Manual.ErrorExplanations.Foo}`.

`````
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
:::errorExample "Description Should Use Headline Case"
```broken
example := x
````

```output
Unknown identifier `x`
```

```fixed
def x := 19
example := x
```

...optional short discussion of example...
:::
`````
