/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Manual.Meta
import Manual.Interaction.FormatRepr

open Lean.MessageSeverity

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Ranges" =>
%%%
tag := "ranges"
%%%

A {deftech}_range_ represents a ...


:::syntax term (title := "Range Syntax")
Ranges consist of a starting point, `...`, and an ending point.
The starting point may be either `*`, which denotes a range that continues infinitely downwards, or a term, which denotes a range with a specific starting value.
By default, ranges are left-closed: they contain their starting points.
A trailing `<` indicates that the range is left-open and does not contain its starting point.
The ending point may be `*`, in which case the range continues infinitely upwards, or a term, which denotes a range with a specific ending value.
By default, ranges are right-open: they do not contain their ending points.
The ending point may be prefixed with `<` to indicate that it is right-open; this is the default and does not change the meaning, but may be easier to read.
It may also be prefixed with `=` to indicate that the range is right-closed and contains its ending point.

This range is left-closed, right-open, and indicates {name}`Std.Rco`:
```grammar
$a...$b
```

This range is left-closed, right-open, and indicates {name}`Std.Rco`:
```grammar
$a...<$b
```

This range is left-closed, right-closed, and indicates {name}`Std.Rcc`:
```grammar
$a...=$b
```

This range is left-closed, right-infinite, and indicates {name}`Std.Rci`:
```grammar
$a...*
```

This range is left-open, right-open, and indicates {name}`Std.Roo`:
```grammar
$a<...$b
```

This range is left-open, right-open, and indicates {name}`Std.Roo`:
```grammar
$a<...<$b
```

This range is left-open, right-closed, and indicates {name}`Std.Roc`:
```grammar
$a<...=$b
```
This range is left-open, right-infinite, and indicates {name}`Std.Roi`:
```grammar
$a<...*
```
This range is left-infinite, right-open, and indicates {name}`Std.Rio`:
```grammar
*...$b
```

This range is left-infinite, right-open, and indicates {name}`Std.Ric`:
```grammar
*...<$b
```

This range is left-infinite, right-closed, and indicates {name}`Std.Ric`:
```grammar
*...=$b
```

This range is infinite on both sides, and indicates {name}`Std.Rii`:
```grammar
*...*
```
:::

# Range Types

{docstring Std.Rco +allowMissing}

{docstring Std.Rco.iter}

{docstring Std.Rco.toArray}

{docstring Std.Rco.toList}

{docstring Std.Rco.size}

{docstring Std.Rco.isEmpty}

{docstring Std.Rcc +allowMissing}

{docstring Std.Rcc.iter}

{docstring Std.Rcc.toArray}

{docstring Std.Rcc.toList}

{docstring Std.Rcc.size}

{docstring Std.Rcc.isEmpty}

{docstring Std.Rci +allowMissing}

{docstring Std.Rci.iter}

{docstring Std.Rci.toArray}

{docstring Std.Rci.toList}

{docstring Std.Rci.size}

{docstring Std.Rci.isEmpty}

{docstring Std.Roo +allowMissing}

{docstring Std.Roo.iter}

{docstring Std.Roo.toArray}

{docstring Std.Roo.toList}

{docstring Std.Roo.size}

{docstring Std.Roo.isEmpty}

{docstring Std.Roc +allowMissing}

{docstring Std.Roc.iter}

{docstring Std.Roc.toArray}

{docstring Std.Roc.toList}

{docstring Std.Roc.size}

{docstring Std.Roc.isEmpty}

{docstring Std.Roi +allowMissing}

{docstring Std.Roi.iter}

{docstring Std.Roi.toArray}

{docstring Std.Roi.toList}

{docstring Std.Roi.size}

{docstring Std.Roi.isEmpty}

{docstring Std.Rio +allowMissing}

{docstring Std.Rio.iter}

{docstring Std.Rio.toArray}

{docstring Std.Rio.toList}

{docstring Std.Rio.size}

{docstring Std.Rio.isEmpty}

{docstring Std.Ric +allowMissing}

{docstring Std.Ric.iter}

{docstring Std.Ric.toArray}

{docstring Std.Ric.toList}

{docstring Std.Ric.size}

{docstring Std.Ric.isEmpty}

{docstring Std.Rii}

{docstring Std.Rii.iter}

{docstring Std.Rii.toArray}

{docstring Std.Rii.toList}

{docstring Std.Rii.size}

{docstring Std.Rii.isEmpty}

# Range-Related Type Classes

{docstring Std.PRange.UpwardEnumerable}

{docstring Std.PRange.LawfulUpwardEnumerable}

{docstring Std.PRange.UpwardEnumerable.LE}

{docstring Std.PRange.UpwardEnumerable.LT}

{docstring Std.PRange.Least?}

{docstring Std.PRange.InfinitelyUpwardEnumerable +allowMissing}

{docstring Std.PRange.LinearlyUpwardEnumerable +allowMissing}
