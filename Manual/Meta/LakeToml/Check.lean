/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module
public import ManualLakeTest.PackageTest
public import Lake.Load.Toml
public import Lake.Toml.Load
public import Lean.Data.Lsp.Utf16
public import Lean.Parser.Extension

public section

open Lean Elab

namespace Manual

namespace Toml


open Lake Toml in
def report [Monad m] [Lean.MonadLog m] [MonadFileMap m] [Test α] (val : α) (errs : Array DecodeError) : m String := do
    let mut result := ""
    unless errs.isEmpty do
      result := result ++ "Errors:\n"
      for e in errs do
        result := result ++ (← posStr e.ref) ++ e.msg ++ "\n"
      result := result ++ "-------------\n"
    result := result ++ (Test.toString val).pretty ++ "\n"
    pure result
where
  posStr (stx : Syntax) : m String := do
    let text ← getFileMap
    let fn ← getFileName <&> (System.FilePath.fileName · |>.getD "")
    let head := (stx.getHeadInfo? >>= SourceInfo.getPos?) <&> text.utf8PosToLspPos
    let tail := (stx.getTailInfo? >>= SourceInfo.getPos?) <&> text.utf8PosToLspPos
    if let some ⟨l, c⟩ := head then
      if let some ⟨l', c'⟩ := tail then
        if l = l' then return s!"{fn}:{l}:{c}-{c'}: "
        else return s!"{fn}:{l}-{l'}:{c}-{c'}: "
      return s!"{fn}:{l}:{c}: "
    return ""
end Toml

section

variable [Monad m] [MonadLiftT BaseIO m] [MonadFileMap m] [Lean.MonadLog m]

open Lean.Parser in
open Lake Toml in
def checkToml (α : Type)  [Inhabited α] [DecodeToml α] [Toml.Test α] (str : String) (what : Name) : m (Except String String) := do
  let ictx := mkInputContext str "<example TOML>"
  match (← Lake.Toml.loadToml ictx |>.toBaseIO) with
  | .error err =>
    return .error <| toString (← err.unreported.toArray.mapM (·.toString))
  | .ok tbl =>
    let .ok (out : α) errs := (tbl.tryDecode what).run #[]
    .ok <$> report out errs

structure Named (α : Name → Type u) where
  name : Name
  val : α name

instance [(n : Name) → Toml.Test (α n)] : Toml.Test (Named α) where
  toString
    | ⟨n, v⟩ => "{ " ++ .group (.nest 2 <| "name := " ++ n.toString ++ "," ++ .line ++ "val := " ++ Toml.Test.toString v ++ "}")

instance [(n : Name) →  Lake.DecodeToml (α n)] : Lake.DecodeToml (Named α) where
  decode v := do
    let table ← v.decodeTable --
    let name ← Lake.stringToLegalOrSimpleName <$> table.decode `name
    let val ← Lake.DecodeToml.decode v
    return ⟨name, val⟩

open Lean.Parser in
open Lake Toml in
private def checkTomlArrayWithName (α : Name → Type) [(n : Name) → Inhabited (α n)] [(n : Name) → DecodeToml (α n)] [(n : Name) → Toml.Test (α n)] (str : String) (what : Name) : m (Except String String) := do
  let ictx := mkInputContext str "<example TOML>"
  match (← Lake.Toml.loadToml ictx |>.toBaseIO) with
  | .error err =>
    return .error <| toString (← err.unreported.toArray.mapM (·.toString))
  | .ok tbl =>
    let .ok (name : Name) errs := (tbl.tryDecode `name).run #[]
    let .ok out errs := (tbl.tryDecode what).run errs
    .ok <$> report (out : α name) errs


-- TODO this became private upstream, so it's been copied to fix the build.
-- Negotiate a public API.
open Lake Toml in
private def decodeTargetDecls
  (pkg : Name) (t : Table)
: DecodeM (Array (PConfigDecl pkg) × DNameMap (NConfigDecl pkg)) := do
  let r := (#[], {})
  let r ← go r LeanLib.keyword LeanLib.configKind LeanLibConfig.decodeToml
  let r ← go r LeanExe.keyword LeanExe.configKind LeanExeConfig.decodeToml
  let r ← go r InputFile.keyword InputFile.configKind InputFileConfig.decodeToml
  let r ← go r InputDir.keyword InputDir.configKind InputDirConfig.decodeToml
  return r
where
  go r kw kind (decode : {n : Name} → Table → DecodeM (ConfigType kind pkg n)) := do
    let some tableArrayVal := t.find? kw | return r
    let some vals ← tryDecode? tableArrayVal.decodeValueArray | return r
    vals.foldlM (init := r) fun r val => do
      let some t ← tryDecode? val.decodeTable | return r
      let some name ← tryDecode? <| stringToLegalOrSimpleName <$> t.decode `name
        | return r
      let (decls, map) := r
      if let some orig := map.get? name then
        modify fun es => es.push <| .mk val.ref s!"\
          {pkg}: target '{name}' was already defined as a '{orig.kind}', \
          but then redefined as a '{kind}'"
        return (decls, map)
      else
        let config ← @decode name t
        let decl : NConfigDecl pkg name :=
          -- Safety: By definition, config kind = facet kind for declarative configurations.
          unsafe {pkg, name, kind, config, wf_data := lcProof}
        return (decls.push decl.toPConfigDecl, map.insert name decl)

open Lean.Parser in
open Lake Toml in
def checkTomlPackage [Lean.MonadError m] (str : String) : m (Except String String) := do
  let ictx := mkInputContext str "<example TOML>"
  match (← Lake.Toml.loadToml ictx |>.toBaseIO) with
  | .error err =>
    return .error <| toString (← err.unreported.toArray.mapM (·.toString))
  | .ok tbl =>
    let .ok env ←
      EIO.toBaseIO <|
        Lake.Env.compute {home:=""} {sysroot:=""} none none
      | throwError "Failed to make env"
    let cfg : LoadConfig := {lakeEnv := env, wsDir := "."}
    let .ok (pkg : Lake.Package) errs := Id.run <| (EStateM.run · #[]) <| do
      let name ← stringToLegalOrSimpleName <$> tbl.tryDecode `name
      let config : PackageConfig name name ← PackageConfig.decodeToml tbl
      let (targetDecls, targetDeclMap) ← decodeTargetDecls name tbl
      let defaultTargets ← tbl.tryDecodeD `defaultTargets #[]
      let defaultTargets := defaultTargets.map stringToLegalOrSimpleName
      let depConfigs ← tbl.tryDecodeD `require #[]
      pure {
        dir := cfg.pkgDir
        relDir := cfg.relPkgDir
        relConfigFile := cfg.relConfigFile
        scope := cfg.scope
        remoteUrl := cfg.remoteUrl
        configFile := cfg.configFile
        config, depConfigs, targetDecls, targetDeclMap
        defaultTargets
        baseName := name
        wsIdx := 0
        origName := name
        keyName := name
        relManifestFile := Lake.defaultManifestFile
      }

    .ok <$> report pkg errs

end
