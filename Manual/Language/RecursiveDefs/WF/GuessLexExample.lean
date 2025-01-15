/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joachim Breitner
-/

import VersoManual

import Manual.Meta

/-!
This is extracted into its own file because line numbers show up in the error message, and we don't
want to update it over and over again as we edit the large file.
-/

open Verso.Genre Manual
open Lean.Elab.Tactic.GuardMsgs.WhitespaceMode

#doc (Manual) "Termination failure (for inclusion elsewhere)" =>

:::example "Termination failure"

If we omit the {keywordOf Lean.Parser.Command.declaration}`termination_by` clause, Lean attempts to infer termination, and if it fails prints the table mentioned above. We include a  {keywordOf Lean.Parser.Command.declaration}`decreasing_by` clause simply to prevent Lean from also attempting structural recursion, to keep the error message to the point.

```lean (error := true) (keep := false) (name := badwf)
def f : (n m l : Nat) → Nat
  | n+1, m+1, l+1 => [
      f (n+1) (m+1) (l+1),
      f (n+1) (m-1) (l),
      f (n)   (m+1) (l) ].sum
  | _, _, _ => 0
decreasing_by all_goals decreasing_tactic
```
```leanOutput badwf (whitespace := lax)
Could not find a decreasing measure.
The arguments relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
           n m l
1) 28:6-25 = = =
2) 29:6-23 = < _
3) 30:6-23 < _ _
Please use `termination_by` to specify a decreasing measure.
```

This message conveys the following facts:

* In the first recursive call, all arguments are (provably) equal to the parameters
* In the second recursive call, the first argument is equal and the second argument is provably smaller than the second parameter. The third parameter was not investigated for this recursive call, because it was not necessary to determine that no suitable termination argument exists.
* In the third recursive call, the first argument decreases strictly, and the other arguments were not looked at.

To investigate why these termination proofs failed it is recommended to explicitly indicate the expected termination argument using {keywordOf Lean.Parser.Command.declaration}`termination_by`. This will surface the messages from the failing tactic.

:::
