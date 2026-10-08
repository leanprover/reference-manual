/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module
public import Verso.Doc.Elab

public meta import Manual.Meta.Basic
public import Verso.Log
public meta import VersoManual.InlineLean.Outputs
import VersoManual.InlineLean

public section

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

meta instance : FromArgs ModuleConfig m where
  fromArgs := ModuleConfig.mk <$> .named' `name true <*> .named' `moduleName true <*> .flag `error false <*> .flag `show true

end

section
open SubVerso.Highlighting
meta partial def getMessages (hl : Highlighted) : Array (Nat × Highlighted.Message) :=
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

meta def dropBlanks (hl : Highlighted) : Highlighted :=
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

meta section

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

/--
The number of external processes that an example directive runs at once. It is read from the
environment variable `MANUAL_EXAMPLE_JOBS`, and defaults to 4.
-/
def exampleJobs : IO Nat := do
  let n := (← IO.getEnv "MANUAL_EXAMPLE_JOBS").bind (·.toNat?) |>.getD 4
  return max n 1

private abbrev PipedChild := IO.Process.Child { stdin := .null, stdout := .piped, stderr := .piped }

/--
Runs the processes described by `procs`, at most `exampleJobs` at a time, and returns their
outputs in the same order. A process's standard input is the corresponding element of `inputs`,
if there is one; otherwise the process has no standard input, as with `IO.Process.output`.

While waiting, elaboration is checked for interruption. However this returns, including by
interruption or an error, any process that is still running is killed and reaped first, so the
caller may remove the directory that the processes work in. Each process is started in its own
process group, and killing it kills the whole group, so tools that start further processes, such as
Lake, are stopped along with everything they started.
-/
def outputsConcurrently (procs : Array IO.Process.SpawnArgs)
    (inputs : Array (Option String) := #[]) : DocElabM (Array IO.Process.Output) := do
  let limit ← exampleJobs
  -- The children that have not been reaped, kept outside the loop's state for the cleanup below.
  let live ← IO.mkRef (#[] : Array PipedChild)
  let mut results : Array (Option IO.Process.Output) := Array.replicate procs.size none
  let mut next := 0
  let mut running : Array (Nat × PipedChild × Task (Except IO.Error String) ×
      Task (Except IO.Error String)) := #[]
  try
    while next < procs.size || !running.isEmpty do
      while running.size < limit do
        let some proc := procs[next]? | break
        let child : PipedChild ←
          match (inputs[next]?).join with
          | none =>
            IO.Process.spawn {
              proc with stdin := .null, stdout := .piped, stderr := .piped, setsid := true
            }
          | some input => do
            let (stdin, child) ← (← IO.Process.spawn {
              proc with stdin := .piped, stdout := .piped, stderr := .piped, setsid := true
            }).takeStdin
            -- The input is written concurrently, and the pipe is closed when the task finishes and
            -- releases its handle.
            discard <| IO.asTask (prio := .dedicated) do
              stdin.putStr input
              stdin.flush
            pure child
        -- The pipes are drained concurrently so that a child with a lot of output cannot block.
        let stdout ← IO.asTask child.stdout.readToEnd .dedicated
        let stderr ← IO.asTask child.stderr.readToEnd .dedicated
        running := running.push (next, child, stdout, stderr)
        live.set (running.map (·.2.1))
        next := next + 1
      let mut stillRunning := #[]
      for r in running do
        let (i, child, stdout, stderr) := r
        match ← child.tryWait with
        | some exitCode =>
          let stdout ← IO.ofExcept stdout.get
          let stderr ← IO.ofExcept stderr.get
          results := results.set! i (some { exitCode, stdout, stderr })
        | none => stillRunning := stillRunning.push r
      running := stillRunning
      live.set (running.map (·.2.1))
      unless running.isEmpty do
        Core.checkInterrupted
        IO.sleep 10
  finally
    for child in ← live.get do
      try child.kill catch _ => pure ()
      discard <| child.wait
  return results.filterMap id

/--
Runs a single process as `outputsConcurrently` does, killing it if elaboration is interrupted.
-/
def outputInterruptibly (proc : IO.Process.SpawnArgs) (input? : Option String := none) :
    DocElabM IO.Process.Output := do
  let #[out] ← outputsConcurrently #[proc] #[input?]
    | throwError "Expected exactly one process output"
  return out

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
      let out ← outputInterruptibly {cmd := "lake", args := #["env", "which", "subverso-extract-mod"]}
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
      let out ← outputInterruptibly {
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

end

structure IdentRefConfig where
  name : Ident

section
variable [Monad m] [MonadError m]
meta instance : FromArgs IdentRefConfig m where
  fromArgs := IdentRefConfig.mk <$> .positional' `name
end

@[code_block]
meta def identRef : CodeBlockExpanderOf IdentRefConfig
  | { name := x }, _ => pure x

@[role identRef]
meta def identRefRole : RoleExpanderOf IdentRefConfig
  | { name := x }, _ => pure x

structure ModulesConfig where
  server : Bool
  moduleRoots : List Ident
  error : Bool

section
variable [Monad m] [MonadError m]
meta instance : FromArgs ModulesConfig m where
  fromArgs := ModulesConfig.mk <$> .flag `server true <*> .many (.named' `moduleRoot false) <*> .flag `error false
end

meta section

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

/--
Rewrites the `{name}` roles in `blocks` to refer to names defined in `code`.

Returns the rewritten blocks together with a function that wraps a term elaborated from them in the
bindings that the rewritten roles expect. A name that `code` does not define is reported as an
error and rendered as plain code.
-/
def resolveNameRoles (blocks : Array Syntax) (code : SubVerso.Highlighting.Highlighted) :
    DocElabM (Array Syntax × (Term → DocElabM Term)) := do
  let (blocks, quotes) ← blocks.mapM getQuotes |>.run {}
  let mut wrap : Term → DocElabM Term := pure
  for (x, q) in quotes do
    let inline ←
      if let some tok := code.matchingName? q.getString then
        let hl : Term := quote (SubVerso.Highlighting.Highlighted.token tok)
        `(Verso.Doc.Inline.other
            {Verso.Genre.Manual.InlineLean.Inline.name with data := ToJson.toJson $hl}
            #[Verso.Doc.Inline.code $(quote q.getString)])
      else
        logErrorAt q m!"Not found in the example's code: {q.getString.quote}"
        `(Verso.Doc.Inline.code $(quote q.getString))
    wrap := wrap >=> fun stx => `(let $(mkIdent x) := $inline; $stx)
  return (blocks, wrap)

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

end

@[directive]
meta def leanModules : DirectiveExpanderOf ModulesConfig
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

    let out ← outputInterruptibly {cmd := "lake", args := #["env", "which", "subverso-extract-mod"]}
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

      let out ← outputInterruptibly {
        cmd := "lake", args := #["build"], cwd := some dirname
        -- `subverso-extract-mod` reads `.olean` files from the build directory, which the local artifact
        -- cache leaves empty unless artifacts are restored
        env := #[("LAKE_RESTORE_ARTIFACTS", "true")]
      }
      if !error && out.exitCode != 0 then
        throwError
          m!"When running 'lake build' in {dirname}, the exit code was {out.exitCode}\n" ++
          m!"Stderr:\n{out.stderr}\n\nStdout:\n{out.stdout}\n\n"
      else
        logBuild "lake build" out

      let mut addLets : Term → DocElabM Term := fun stx => pure stx
      let mut hasError := false
      let mut allHl := .empty

      let jsonFile (modName : Name) := dirname / (modName.toString : System.FilePath).addExtension "json"
      let srcPath := dirname.toString ++ ((":" ++ ·) <$> (← IO.getEnv "LEAN_SRC_PATH")).getD ""
      let leanPath := (dirname / ".lake" / "build" / "lib" / "lean").toString ++
        ((":" ++ ·) <$> (← IO.getEnv "LEAN_PATH")).getD ""
      let outs ← outputsConcurrently <| mods.map fun (modName, _, _, _) => {
        cmd := toString «subverso-extract-mod»,
        args := (if server then #[] else #["--not-server"]) ++ #[modName.toString, (jsonFile modName).toString],
        cwd := some dirname
        env := #[("LEAN_SRC_PATH", srcPath), ("LEAN_PATH", leanPath)]
      }

      for ((modName, x, modConfig, blame), out) in mods.zip outs do
        let jsonFile := jsonFile modName
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

      let (blocks, wrapNames) ← resolveNameRoles blocks allHl
      let body ← blocks.mapM (elabBlock <| ⟨·⟩)
      let body ← `(Verso.Doc.Block.concat #[$body,*])
      addLets (← wrapNames body)


where
  lakefile (roots : List Name) : String := Id.run do
    let libNames := roots.map fun n => n.toString.quote
    let namesList := ", ".intercalate libNames
    let mut content := s!"name = \"example\"\ndefaultTargets = [{namesList}]\n"
    for lib in libNames do
      content := content ++ "\n[[lean_lib]]\nname = " ++ lib ++ "\n"
    return content

  mkImports (root : Name) (mods : Array Name) : String :=
    "module\n" ++
    String.join (mods |>.filter (root.isPrefixOf ·) |>.toList |>.map (s!"import {·}\n"))
