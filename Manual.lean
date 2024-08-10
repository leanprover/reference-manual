import Verso.Genre.Manual

import Manual.Intro
import Manual.Elaboration
import Manual.Language
import Manual.BuiltInTypes

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "The Lean Language Reference" =>

%%%
authors := ["Lean Developers"]
%%%

{include Manual.Intro}

{include Manual.Elaboration}

{include Manual.Language}

{include Manual.BuiltInTypes}


# Progress

:::progress
```namespace
String Char Nat
```
```exceptions
String.revFindAux String.extract.go₂ String.substrEq.loop String.casesOn
String.offsetOfPosAux String.extract.go₁ String.mapAux String.firstDiffPos.loop String.utf8SetAux String.revPosOfAux String.replace.loop
String.rec String.recOn String.posOfAux String.splitAux String.foldrAux
String.splitOnAux String.intercalate.go String.anyAux String.findAux
String.utf8GetAux? String.foldlAux String.utf8GetAux
String.utf8PrevAux String.noConfusionType String.noConfusion
String.utf8ByteSize.go String.validateUTF8.loop
String.crlfToLf.go
String.fromUTF8.loop
String.one_le_csize
```

```exceptions
String.sluggify
```

```exceptions
Nat.anyM.loop
Nat.nextPowerOfTwo.go
Nat.foldRevM.loop
Nat.foldM.loop
Nat.foldTR.loop
Nat.recAux
Nat.allTR.loop
Nat.allM.loop
Nat.anyTR.loop
Nat.anyM.loop
Nat.toSuperDigitsAux
Nat.casesAuxOn
Nat.forM.loop
Nat.repeatTR.loop
Nat.forRevM.loop
Nat.toSubDigitsAux
```

```exceptions
Nat.one_pos
Nat.not_lt_of_lt
Nat.sub_lt_self
Nat.lt_or_gt
Nat.pow_le_pow_left
Nat.not_lt_of_gt
Nat.le_or_le
Nat.le_or_ge
Nat.pred_lt'
Nat.pow_le_pow_right
Nat.lt_iff_le_and_not_ge
Nat.mul_pred_right
Nat.mul_pred_left
Nat.prod_dvd_and_dvd_of_dvd_prod
Nat.lt_iff_le_and_not_ge
Nat.mul_pred_right
```

```exceptions
Nat.binductionOn
Nat.le.rec
Nat.le.recOn
Nat.le.casesOn
Nat.le.below
Nat.le.below.step
Nat.le.below.rec
Nat.le.below.recOn
Nat.le.below.refl
Nat.le.below.casesOn
```

:::


# Index
%%%
number := false
%%%

{theIndex}
