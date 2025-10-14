import Manual.Meta.Example
import VersoManual
open Lean
open Verso Doc Multi
open Verso.Genre Manual
open Std (HashMap)

/--
In the `Array (Array String × String)`, the first string is path to
the example file we're writing, and the second is the body of the example.
-/
abbrev ExtractM := ReaderT (Array String) (StateT (Array (Array String × String)) IO)

partial def extractExamples (_mode : Mode) (logError : String → IO Unit) (cfg : Manual.Config) (_state : TraverseState) (text : Part Manual) : IO Unit := do

  let code := (← part text |>.run #[] |>.run #[]).snd
  let dest := cfg.destination / "extracted-examples"
  for (ctx, content) in code do

    let filename := ctx.map (Slug.toString ∘ String.sluggify)
      |>.foldl (init := dest) (· / ·)
      |>.withExtension "lean"
    filename.parent.forM IO.FS.createDirAll
    IO.FS.writeFile filename content

where
  part : Part Manual → ExtractM Unit
    | .mk _ titleString _ intro subParts => withReader (·.push titleString) do
      for b in intro do block b
      for p in subParts do part p
  block : Block Manual → ExtractM Unit
    | .other which contents => do
      if which.name == `Manual.example then
        match FromJson.fromJson? which.data (α := Manual.ExampleBlockJson) with
        | .error e => logError s!"Error deserializing example data: {e}"
        | .ok (descrString, _, _, _, liveText) =>
          let context ← read
          let some txt := liveText
            | return ()
          modify fun saved =>
            saved.push (context.push descrString, txt)
      for b in contents do block b
    | .concat bs | .blockquote bs =>
      for b in bs do block b
    | .ol _ lis | .ul lis =>
      for li in lis do
        for b in li.contents do block b
    | .dl dis =>
      for di in dis do
        for b in di.desc do block b
    | .para .. | .code .. => pure ()
