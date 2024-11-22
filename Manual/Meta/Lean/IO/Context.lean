import Lean.Environment

namespace Manual.IOExample

open Lean

structure IOExampleContext where
  leanCodeName : Ident
  code : Option StrLit := none
  inputFiles : Array (System.FilePath × StrLit) := #[]
  outputFiles : Array (System.FilePath × StrLit) := #[]
  stdin : Option StrLit := none
  stdout : Option StrLit := none
  stderr : Option StrLit := none
deriving Repr

initialize ioExampleCtx : EnvExtension (Option IOExampleContext) ←
  Lean.registerEnvExtension (pure none)
