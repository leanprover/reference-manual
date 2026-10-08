/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module
public import Verso.Doc.Elab.Monad
public meta import Verso.Doc.Elab.Monad
public meta import Lean.Linter.CodeQuality

public section

open Lean
open Lean.Linter.CodeQuality
open Verso Doc Elab

namespace Manual

meta section

deriving instance FromJson for Lean.Linter.CodeQuality.Source
deriving instance FromJson for Lean.Linter.CodeQuality.Value
deriving instance FromJson for Lean.Linter.CodeQuality.Entry

/-- Parses a sequence of JSON values, which is the format that `lake lint --code-quality` emits. -/
private def parseJsonStream (s : String) : Except String (Array Json) :=
  let p : Std.Internal.Parsec.String.Parser (Array Json) := do
    Std.Internal.Parsec.String.ws
    let values ← Std.Internal.Parsec.many Json.Parser.anyCore
    Std.Internal.Parsec.eof
    return values
  p.run s

/--
A sequence of code quality metric entries in the format emitted by `lake lint --code-quality`.

Each JSON value in the block must deserialize as a `Lean.Linter.CodeQuality.Entry`, and
serializing the result with the compiler's own instance must reproduce the value.
-/
@[code_block]
def codeQualityEntries : CodeBlockExpanderOf Unit
  | (), str => do
    let text := str.getString
    let values ←
      match parseJsonStream text with
      | .error e => throwErrorAt str m!"Expected a sequence of JSON values: {e}"
      | .ok values => pure values
    if values.isEmpty then
      throwErrorAt str "Expected at least one entry"
    for value in values do
      let entry : Entry ←
        match fromJson? value with
        | .error e => throwErrorAt str m!"Not a code quality entry: {e}{indentD value.pretty}"
        | .ok entry => pure entry
      let serialized := toJson entry
      unless value.compress == serialized.compress do
        throwErrorAt str
          m!"Entry does not round-trip through the compiler's serializer.\n\
            Given:{indentD value.pretty}\nSerialized:{indentD serialized.pretty}"
    ``(Verso.Doc.Block.code $(quote text))

end

end Manual
