/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Elab.Term
import Lean.Elab.Tactic

import Verso.Code.Highlighted
import Verso.Doc.Elab
import Verso.Doc.ArgParse
import Verso.Doc.Suggestion
import SubVerso.Highlighting.Code
import SubVerso.Examples.Messages
import VersoManual

import Manual.Meta.Basic
import Manual.Meta.PPrint

open Verso.Doc.Elab
open Verso.ArgParse
open Verso.Log
open Lean

namespace Manual

structure ModuleConfig where
  name : Option Ident := none
  moduleName : Option Ident := none
  error : Bool := false
  «show» : Bool := true

section

variable [Monad m] [MonadError m]

instance : FromArgs ModuleConfig m where
  fromArgs := ModuleConfig.mk <$> .named' `name true <*> .named' `moduleName true <*> .flag `error false <*> .flag `show true

end

section
open SubVerso.Highlighting
partial def getMessages (hl : Highlighted) : Array (Nat × Highlighted.Message) :=
  let ((), _, out) := go hl (0, #[])
  out
where
  go : Highlighted → StateM (Nat × Array (Nat × Highlighted.Message)) Unit
    | .text s | .unparsed s =>
      for c in s.toSlice.chars do
        if c == '\n' then modify fun (l, msgs) => (l + 1, msgs) else pure ()
    | .token .. => pure ()
    | .tactics _ _ _ hl' => go hl'
    | .seq xs => xs.forM go
    | .span msgs' hl' => do
      modify fun (l, msgs) => (l, msgs ++ msgs'.map (fun (sev, m) => (l, ⟨sev, m⟩)))
      go hl'
    | .point sev contents =>
      modify fun (l, msgs) => (l, msgs.push (l, ⟨sev, contents⟩))

def dropBlanks (hl : Highlighted) : Highlighted :=
  match hl with
  | .text s => .text s.trimAsciiStart.copy
  | .seq xs => Id.run do
    for h : i in 0...xs.size do
      let x := dropBlanks xs[i]
      if x.isEmpty then continue
      return .seq <| #[x] ++ xs.extract (i + 1) xs.size
    return .seq #[]
  | _ => hl

end

def logBuild [Monad m] [MonadRef m] [MonadOptions m] [MonadLog m] [AddMessageContext m] (command : String) (out : IO.Process.Output) (blame : Option Syntax := none) : m Unit := do
  let blame ←
    if let some b := blame then pure b else getRef
  let mut buildOut : Array MessageData := #[]
  unless out.stdout.isEmpty do
    buildOut := buildOut.push <| .trace {cls := `stdout} (toMessageData out.stdout) #[]
  unless out.stderr.isEmpty do
    buildOut := buildOut.push <| .trace {cls := `stderr} (toMessageData out.stderr) #[]
  unless buildOut.isEmpty do
    logSilentInfoAt blame <| .trace {cls := `build} m!"{command}" buildOut

def lineStx [Monad m] [MonadFileMap m] (l : Nat) : m Syntax := do
  let text ← getFileMap
  -- 0-indexed vs 1-indexed requires +1 and +2 here
  let r := ⟨text.lineStart (l + 1), text.lineStart (l + 2)⟩
  return .ofRange r

@[code_block]
def leanModule : CodeBlockExpanderOf ModuleConfig
  | { name, moduleName, error, «show» }, str => do
    let line := (← getFileMap).utf8PosToLspPos str.raw.getPos! |>.line
    let leanCode := line.fold (fun _ _ s => s.push '\n') "" ++ str.getString ++ "\n"
    let hl ← IO.FS.withTempDir fun dirname => do
      let u := toString (← IO.monoMsNow)
      let dirname := dirname / u
      IO.FS.createDirAll dirname
      let modName : Name := moduleName.map (·.getId) |>.getD `Main
      let out ← IO.Process.output {cmd := "lake", args := #["env", "which", "subverso-extract-mod"]}
      if out.exitCode != 0 then
        throwError
          m!"When running 'lake env which subverso-extract-mod', the exit code was {out.exitCode}\n" ++
          m!"Stderr:\n{out.stderr}\n\nStdout:\n{out.stdout}\n\n"
      let some «subverso-extract-mod» := out.stdout.splitOn "\n" |>.head?
        | throwError "No executable path found"
      let «subverso-extract-mod» ← IO.FS.realPath «subverso-extract-mod»

      let leanFileName : System.FilePath := (modName.toString : System.FilePath).addExtension "lean"
      IO.FS.writeFile (dirname / leanFileName) leanCode


      let jsonFile := dirname / s!"{modName}.json"
      let out ← IO.Process.output {
        cmd := toString «subverso-extract-mod»,
        args := #[modName.toString, jsonFile.toString],
        cwd := some dirname,
        env := #[("LEAN_SRC_PATH", dirname.toString ++ ((":" ++ ·) <$> (← IO.getEnv "LEAN_SRC_PATH")).getD "") ]
      }
      if out.exitCode != 0 then
        throwError
          m!"When running '{«subverso-extract-mod»} {modName} {jsonFile}' in {dirname}, the exit code was {out.exitCode}\n" ++
          m!"Stderr:\n{out.stderr}\n\nStdout:\n{out.stdout}\n\n"
      logBuild s!"subverso-extract-mod {modName} {jsonFile} (in {dirname})" out
      let json ← IO.FS.readFile jsonFile
      let json ← IO.ofExcept <| Json.parse json
      let mod ← match SubVerso.Module.Module.fromJson? json with
        | .ok v => pure v
        | .error e => throwError m!"Failed to deserialized JSON output as highlighted Lean code. Error: {indentD e}\nJSON: {json}"
      let code := mod.items.map (·.code)
      pure <| code.foldl (init := .empty) fun hl v => hl ++ v

    let msgs := getMessages hl

    let hl := dropBlanks hl

    if let some name := name then
      Verso.Genre.Manual.InlineLean.saveOutputs name.getId (msgs.toList.map (·.2))

    let hasError := msgs.any fun m => m.2.severity == .error

    for (l, msg) in msgs do
      match msg.severity with
      | .info => logSilentInfoAt (← lineStx l)  msg.toString
      | .warning => logSilentAt (← lineStx l) .warning msg.toString
      | .error =>
        if error then logSilentInfoAt (← lineStx l) msg.toString
        else logErrorAt (← lineStx l) msg.toString

    if error && !hasError then
      logError "Error expected in code block, but none detected."
    if !error && hasError then
      logError "No error expected in code block, but one occurred."

    if «show» then
      ``(Verso.Doc.Block.other (Verso.Genre.Manual.InlineLean.Block.lean $(quote hl)) #[])
    else
      ``(Verso.Doc.Block.empty)

structure IdentRefConfig where
  name : Ident

section
variable [Monad m] [MonadError m]
instance : FromArgs IdentRefConfig m where
  fromArgs := IdentRefConfig.mk <$> .positional' `name
end

@[code_block]
def identRef : CodeBlockExpanderOf IdentRefConfig
  | { name := x }, _ => pure x

@[role identRef]
def identRefRole : RoleExpanderOf IdentRefConfig
  | { name := x }, _ => pure x

structure ModulesConfig where
  server : Bool
  moduleRoots : List Ident
  error : Bool

section
variable [Monad m] [MonadError m]
instance : FromArgs ModulesConfig m where
  fromArgs := ModulesConfig.mk <$> .flag `server true <*> .many (.named' `moduleRoot false) <*> .flag `error false
end

open Lean.Doc.Syntax in
partial def getBlocks (block : Syntax) : StateT (NameMap (ModuleConfig × StrLit × Syntax)) DocElabM Syntax := do
  if block.getKind == ``Lean.Doc.Syntax.codeblock then
    if let `(Lean.Doc.Syntax.codeblock|```$x:ident $args* | $s:str ```) := block then
      try
        let x' ← Elab.realizeGlobalConstNoOverloadWithInfo x
        if x' == ``leanModule then
          let n ← mkFreshUserName `code
          let blame := mkNullNode <| #[x] ++ args
          let argVals ← parseArgs args
          let cfg ← fromArgs.run argVals
          modify (·.insert n (cfg, s, blame))
          let x := mkIdentFrom block n
          return ← `(Lean.Doc.Syntax.codeblock|```identRef $x:ident | $(quote "") ```)
      catch
      | _ => pure ()

  match block with
  | .node i k xs => do
    let args ← xs.mapM getBlocks
    return Syntax.node i k args
  | _ => return block

open Lean.Doc.Syntax in
partial def getQuotes (stx : Syntax) : StateT (NameMap StrLit) DocElabM Syntax := do
  if stx.getKind == ``Lean.Doc.Syntax.role then
    if let `(Lean.Doc.Syntax.role|role{$x:ident $args*}[$inls*]) := stx then
      try
        let x' ← Elab.realizeGlobalConstNoOverloadWithInfo x
        if x' == ``Verso.Genre.Manual.InlineLean.name then
          unless args.isEmpty do logErrorAt (mkNullNode args) m!"No arguments expected here"
          let some code ← oneCodeStr? inls
            | return ((← `(.empty)) : Syntax)

          let n ← mkFreshUserName `name
          modify (·.insert n code)
          let x := mkIdentFrom stx n
          return ((← `(Lean.Doc.Syntax.role|role{identRef $x:ident}[])) : Syntax)
      catch
      | _ => pure ()

  match stx with
  | .node i k xs => do
    let args ← xs.mapM getQuotes
    return Syntax.node i k args
  | _ => return stx


def getRoot (mods : NameMap (ModuleConfig × α)) : Option Name :=
  mods.foldl (init := none) fun
    | none, _, ({ moduleName, .. }, _) => moduleName.map (·.getId)
    | some y, _, ({moduleName := some x, ..}, _) => prefix? y x.getId
    | some y, _, ({moduleName := none, ..}, _) => some y
where
  prefix? x y :=
    if x.isPrefixOf y then some x
    else if y.isPrefixOf x then some y
    else none

@[directive]
def leanModules : DirectiveExpanderOf ModulesConfig
  | { server, moduleRoots, error }, blocks => do
    let (blocks, codeBlocks) ← blocks.mapM getBlocks {}
    let moduleRoots ←
      if !moduleRoots.isEmpty then pure <| moduleRoots.map (·.getId)
      else if let some root := getRoot codeBlocks then pure [root]
      else
        if codeBlocks.isEmpty then throwError m!"No `{.ofConstName ``leanModule}` blocks in example"
        else
          let mods := codeBlocks.values.filterMap fun ({moduleName, ..}, _) => moduleName
          if mods.isEmpty then
            let msg := m!"No named modules in example." ++ (← m!"Use the named argument `moduleName` to specify a name.".hint #[])
            throwError msg
          let mods := mods.map (m!"`{·}`")
          throwError m!"No root module found for {.andList mods}. Use the `moduleRoot` named argument to generate one."

    let out ← IO.Process.output {cmd := "lake", args := #["env", "which", "subverso-extract-mod"]}
    if out.exitCode != 0 then
      throwError
        m!"When running 'lake env which subverso-extract-mod', the exit code was {out.exitCode}\n" ++
        m!"Stderr:\n{out.stderr}\n\nStdout:\n{out.stdout}\n\n"
    let some «subverso-extract-mod» := out.stdout.splitOn "\n" |>.head?
      | throwError "No executable path found"

    IO.FS.withTempDir fun dirname => do
      let u := toString (← IO.monoMsNow)
      let dirname := dirname / u
      IO.FS.createDirAll dirname
      let mut mods := #[]
      for (x, modConfig, s, blame) in codeBlocks do
        let some modName := modConfig.moduleName
          | logErrorAt blame "Explicit module name required"
        let modName := modName.getId
        let leanFileName : System.FilePath := (modName.toStringWithSep "/" false : System.FilePath).addExtension "lean"
        leanFileName.parent.forM (IO.FS.createDirAll <| dirname / ·)
        IO.FS.writeFile (dirname / leanFileName) (← parserInputString s)
        mods := mods.push (modName, x, modConfig, blame)

      let lakefile.toml := lakefile moduleRoots
      logSilentInfo <| .trace { cls := `lakefile } m!"lakefile.toml" #[lakefile.toml]
      IO.FS.writeFile (dirname / "lakefile.toml") lakefile.toml
      let toolchain : String ← IO.FS.readFile "lean-toolchain"
      IO.FS.writeFile (dirname / "lean-toolchain") toolchain

      let rootsNotPresent := moduleRoots.filter (fun root => !mods.any (fun (x, _, _, _) => x == root))
      for root in rootsNotPresent do
        let leanFileName : System.FilePath := (root.toStringWithSep "/" false : System.FilePath).addExtension "lean"
        leanFileName.parent.forM (IO.FS.createDirAll <| dirname / ·)

        IO.FS.writeFile (dirname / leanFileName) <|
          mkImports root <| mods.map fun (x, _, _, _) => x

      let out ← IO.Process.output {cmd := "lake", args := #["build"], cwd := some dirname}
      if !error && out.exitCode != 0 then
        throwError
          m!"When running 'lake build' in {dirname}, the exit code was {out.exitCode}\n" ++
          m!"Stderr:\n{out.stderr}\n\nStdout:\n{out.stdout}\n\n"
      else
        logBuild "lake build" out

      let mut addLets : Term → DocElabM Term := fun stx => pure stx
      let mut hasError := false
      let mut allHl := .empty

      for (modName, x, modConfig, blame) in mods do

        let jsonFile := dirname / (modName.toString : System.FilePath).addExtension "json"
        let out ← IO.Process.output {
          cmd := toString «subverso-extract-mod»,
          args := (if server then #[] else #["--not-server"]) ++ #[modName.toString, jsonFile.toString],
          cwd := some dirname
          env := #[
            ("LEAN_SRC_PATH", dirname.toString ++ ((":" ++ ·) <$> (← IO.getEnv "LEAN_SRC_PATH")).getD ""),
            ("LEAN_PATH", (dirname / ".lake" / "build" / "lib" / "lean").toString ++ ((":" ++ ·) <$> (← IO.getEnv "LEAN_PATH")).getD "")
          ]
        }
        if out.exitCode != 0 then
          throwError
            m!"When running '{«subverso-extract-mod»} {modName} {jsonFile}' in {dirname}, the exit code was {out.exitCode}\n" ++
            m!"Stderr:\n{out.stderr}\n\nStdout:\n{out.stdout}\n\n"
        logBuild s!"subverso-extract-mod {modName} {jsonFile} (in {dirname}, exit code {out.exitCode})" out (some blame)

        let json ← IO.FS.readFile (dirname / jsonFile)

        let json ← IO.ofExcept <| Json.parse json
        let code ← match SubVerso.Module.Module.fromJson? json with
          | .ok v => pure (v.items.map (·.code))
          | .error e => throwError m!"Failed to deserialized JSON output as highlighted Lean code. Error: {indentD e}\nJSON: {json}"
        let hl := code.foldl (init := .empty) fun hl v => hl ++ v

        let msgs := getMessages hl
        let hl := dropBlanks hl
        allHl := allHl ++ hl

        if let some name := modConfig.name then
          Verso.Genre.Manual.InlineLean.saveOutputs name.getId <| msgs.toList.map (·.2)

        hasError := hasError || msgs.any fun m => m.2.severity == .error

        for (l, msg) in msgs do
          match msg.severity with
          | .info => logSilentInfoAt (← lineStx l) msg.toString
          | .warning => logSilentAt (← lineStx l) .warning msg.toString
          | .error =>
            if error then logSilentAt (← lineStx l) .warning msg.toString
            else logErrorAt (← lineStx l) msg.toString

        let filename : System.FilePath := (modName.toStringWithSep "/" false : System.FilePath).addExtension "lean"
        let hlBlk ← ``(Verso.Doc.Block.other (Verso.Genre.Manual.InlineLean.Block.lean $(quote hl) $(quote filename)) #[])
        let hlBlk ← ``(Verso.Doc.Block.other (Verso.Genre.Manual.InlineLean.Block.exampleLeanFile $(quote filename.toString)) #[$hlBlk])
        addLets := addLets >=> fun stx => do
          `(let $(mkIdent x) := $hlBlk; $stx)

      if error && !hasError then
        logError "Error expected in code block, but none detected."
      if !error && hasError then
        logError "No error expected in code block, but one occurred."

      let (blocks, quotes) ← blocks.mapM getQuotes |>.run {}
      for (x, q) in quotes do
        if let some tok := allHl.matchingName? q.getString then
          addLets := addLets >=> fun stx => do
            let hl : SubVerso.Highlighting.Highlighted := .token tok
            let hl : Term := quote hl
            let name ← `(Verso.Doc.Inline.other {Verso.Genre.Manual.InlineLean.Inline.name with data := ToJson.toJson $hl} #[Verso.Doc.Inline.code $(quote q.getString)])
            `(let $(mkIdent x) := $name; $stx)
        else logErrorAt q m!"Not found: {q.getString.quote}"
      let body ← blocks.mapM (elabBlock <| ⟨·⟩)
      let body ← `(Verso.Doc.Block.concat #[$body,*])
      addLets body


where
  lakefile (roots : List Name) : String := Id.run do
    let libNames := roots.map fun n => n.toString.quote
    let namesList := ", ".intercalate libNames
    let mut content := s!"name = \"example\"\ndefaultTargets = [{namesList}]\n"
    content := content ++ "leanOptions = { experimental.module = true }\n"
    for lib in libNames do
      content := content ++ "\n[[lean_lib]]\nname = " ++ lib ++ "\n"
    return content

  mkImports (root : Name) (mods : Array Name) : String :=
    "module\n" ++
    String.join (mods |>.filter (root.isPrefixOf ·) |>.toList |>.map (s!"import {·}\n"))
