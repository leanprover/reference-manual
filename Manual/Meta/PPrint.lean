import Lean.Data.RBMap
import Lean.Data.Json
import Lean.Widget.TaggedText

namespace Manual.Meta.PPrint
open Lean (RBMap)
open Std (Format)

structure FormatWithTags (α : Type u) where
  format : Format
  tags : RBMap Nat α compare

structure TagFormatM.State (α) where
  nextTag : Nat := 0
  tags : RBMap Nat α compare := {}

def TagFormatT α m := StateT (TagFormatM.State α) m

instance [Monad m] : Monad (TagFormatT α m) := inferInstanceAs (Monad (StateT (TagFormatM.State α) m))

scoped instance [Monad m] : MonadStateOf (TagFormatM.State α) (TagFormatT α m) :=
  inferInstanceAs (MonadStateOf (TagFormatM.State α) (StateT (TagFormatM.State α) m))


instance [Functor m] : MonadLift m (TagFormatT α m) where
  monadLift act := fun σ => (·, σ) <$> act

abbrev TagFormatM α := TagFormatT α Id

def TagFormatT.run [Monad m] (act : TagFormatT α m Format) : m (FormatWithTags α) := do
  let (value, ⟨_, tags⟩) ← StateT.run act {}
  pure ⟨value, tags⟩

def TagFormatM.run (act : TagFormatM α Format) : FormatWithTags α := TagFormatT.run act

def fresh [Monad m] : TagFormatT α m Nat :=
  modifyGet fun ⟨i, tags⟩ => (i, ⟨i+1, tags⟩)

def tag [Monad m] (val : α) (doc : Format) : TagFormatT α m Format := do
  let i ← fresh
  modify fun σ => {σ with tags := σ.tags.insert i val}
  pure <| Format.tag i doc

open Lean.Widget

private structure TaggedState (α) where
  out : TaggedText α := .text ""
  tagStack : List (Nat × TaggedText α) := []
  column : Nat := 0
deriving Inhabited

private abbrev RenderM α := (ReaderT (RBMap Nat α compare) (StateM (TaggedState α)))

instance inst [Inhabited α] : Format.MonadPrettyFormat (RenderM α) where
  pushOutput s       := modify fun ⟨out, ts, col⟩ => ⟨out.appendText s, ts, col + s.length⟩
  pushNewline indent := modify fun ⟨out, ts, _⟩ => ⟨out.appendText ("\n".pushn ' ' indent), ts, indent⟩
  currColumn         := return (←get).column
  startTag n         := modify fun ⟨out, ts, col⟩ => ⟨TaggedText.text "", (n, out) :: ts, col⟩
  endTags n          := do
    let tagVals ← read
    modify fun ⟨out, ts, col⟩ =>
      let (ended, left) := (ts.take n, ts.drop n)
      let out' := ended.foldl (init := out) fun acc (tag, top) => top.appendTag (tagVals.find! tag) acc
      ⟨out', left, col⟩

def FormatWithTags.render [Inhabited α] (format : FormatWithTags α) (indent := 0) (w : Nat := Std.Format.defWidth) : TaggedText α :=
  (format.format.prettyM  w indent : RenderM α Unit) format.tags {} |>.2.out

deriving instance Lean.ToJson, Lean.FromJson for TaggedText
deriving instance Lean.ToJson, Lean.FromJson for PUnit

open Lean Syntax in
partial instance [Quote α] : Quote (TaggedText α) where
  quote := go
where
  go
    | .text s => mkCApp ``TaggedText.text #[quote s]
    | .tag x y => mkCApp ``TaggedText.tag #[quote x, go y]
    | .append xs =>
      mkCApp ``TaggedText.append #[arr xs]

  goArr (xs : Array (TaggedText α)) (i : Nat) (args : Array Term) : Term :=
      if h : i < xs.size then
        goArr xs (i+1) (args.push (go xs[i]))
      else
        Syntax.mkCApp (Name.mkStr2 "Array" ("mkArray" ++ toString xs.size)) args

  arr (xs : Array (TaggedText α)) : Term :=
    if xs.size <= 8 then
      goArr xs 0 #[]
    else
      Syntax.mkCApp ``List.toArray #[lst xs.toList]

  lst : List (TaggedText α) → Term
  | []      => mkCIdent ``List.nil
  | (x::xs) => Syntax.mkCApp ``List.cons #[go x, lst xs]
