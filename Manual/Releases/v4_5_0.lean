/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta.Markdown

open Manual
open Verso.Genre


#doc (Manual) "Lean 4.5.0 (2024-02-01)" =>
%%%
tag := "release-v4.5.0"
file := "v4.5.0"
%%%

````markdown
* Modify the lexical syntax of string literals to have string gaps, which are escape sequences of the form `"\" newline whitespace*`.
  These have the interpretation of an empty string and allow a string to flow across multiple lines without introducing additional whitespace.
  The following is equivalent to `"this is a string"`.
  ```lean
  "this is \
     a string"
  ```
  [PR #2821](https://github.com/leanprover/lean4/pull/2821) and [RFC #2838](https://github.com/leanprover/lean4/issues/2838).

* Add raw string literal syntax. For example, `r"\n"` is equivalent to `"\\n"`, with no escape processing.
  To include double quote characters in a raw string one can add sufficiently many `#` characters before and after
  the bounding `"`s, as in `r#"the "the" is in quotes"#` for `"the \"the\" is in quotes"`.
  [PR #2929](https://github.com/leanprover/lean4/pull/2929) and [issue #1422](https://github.com/leanprover/lean4/issues/1422).

* The low-level `termination_by'` clause is no longer supported.

  Migration guide: Use `termination_by` instead, e.g.:
  ```diff
  -termination_by' measure (fun ⟨i, _⟩ => as.size - i)
  +termination_by i _ => as.size - i
  ```

  If the well-founded relation you want to use is not the one that the
  `WellFoundedRelation` type class would infer for your termination argument,
  you can use `WellFounded.wrap` from the std library to explicitly give one:
  ```diff
  -termination_by' ⟨r, hwf⟩
  +termination_by x => hwf.wrap x
  ```

* Support snippet edits in LSP `TextEdit`s. See `Lean.Lsp.SnippetString` for more details.

* Deprecations and changes in the widget API.
  - `Widget.UserWidgetDefinition` is deprecated in favour of `Widget.Module`. The annotation `@[widget]` is deprecated in favour of `@[widget_module]`. To migrate a definition of type `UserWidgetDefinition`, remove the `name` field and replace the type with `Widget.Module`. Removing the `name` results in a title bar no longer being drawn above your panel widget. To add it back, draw it as part of the component using `<details open=true><summary class='mv2 pointer'>{name}</summary>{rest_of_widget}</details>`. See an example migration [here](https://github.com/leanprover/std4/pull/475/files#diff-857376079661a0c28a53b7ff84701afabbdf529836a6944d106c5294f0e68109R43-R83).
  - The new command `show_panel_widgets` allows displaying always-on and locally-on panel widgets.
  - `RpcEncodable` widget props can now be stored in the infotree.
  - See [RFC 2963](https://github.com/leanprover/lean4/issues/2963) for more details and motivation.

* If no usable lexicographic order can be found automatically for a termination proof, explain why.
  See [feat: GuessLex: if no measure is found, explain why](https://github.com/leanprover/lean4/pull/2960).

* Option to print [inferred termination argument](https://github.com/leanprover/lean4/pull/3012).
  With `set_option showInferredTerminationBy true` you will get messages like
  ```
  Inferred termination argument:
  termination_by
  ackermann n m => (sizeOf n, sizeOf m)
  ```
  for automatically generated `termination_by` clauses.

* More detailed error messages for [invalid mutual blocks](https://github.com/leanprover/lean4/pull/2949).

* [Multiple](https://github.com/leanprover/lean4/pull/2923) [improvements](https://github.com/leanprover/lean4/pull/2969) to the output of `simp?` and `simp_all?`.

* Tactics with `withLocation *` [no longer fail](https://github.com/leanprover/lean4/pull/2917) if they close the main goal.

* Implementation of a `test_extern` command for writing tests for `@[extern]` and `@[implemented_by]` functions.
  Usage is
  ```
  import Lean.Util.TestExtern

  test_extern Nat.add 17 37
  ```
  The head symbol must be the constant with the `@[extern]` or `@[implemented_by]` attribute. The return type must have a `DecidableEq` instance.

Bug fixes for
[#2853](https://github.com/leanprover/lean4/issues/2853), [#2953](https://github.com/leanprover/lean4/issues/2953), [#2966](https://github.com/leanprover/lean4/issues/2966),
[#2971](https://github.com/leanprover/lean4/issues/2971), [#2990](https://github.com/leanprover/lean4/issues/2990), [#3094](https://github.com/leanprover/lean4/issues/3094).

Bug fix for [eager evaluation of default value](https://github.com/leanprover/lean4/pull/3043) in `Option.getD`.
Avoid [panic in `leanPosToLspPos`](https://github.com/leanprover/lean4/pull/3071) when file source is unavailable.
Improve [short-circuiting behavior](https://github.com/leanprover/lean4/pull/2972) for `List.all` and `List.any`.

Several Lake bug fixes: [#3036](https://github.com/leanprover/lean4/issues/3036), [#3064](https://github.com/leanprover/lean4/issues/3064), [#3069](https://github.com/leanprover/lean4/issues/3069).

````
