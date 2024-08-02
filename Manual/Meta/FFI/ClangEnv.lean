import Lean.Data.Json
import Lean.Util.Path
import Std.Data.HashMap
import Std.Data.HashSet

open Lean (Json ToJson FromJson)

namespace Manual.Meta.FFI

def ClangId := UInt64

def fromHex (i : String.Iterator) (acc : UInt64) : UInt64 :=
  let c := i.curr
  let acc' := (acc <<< 1) +
    (if '0' ≤ c ∧ c ≤ '9' then
      c.val - '0'.val
    else if 'a' ≤ c ∧ c ≤ 'f' then
      c.val - 'a'.val + 10
    else if 'A' ≤ c ∧ c ≤ 'F' then
      c.val - 'A'.val + 10
    else panic! s!"Invalid hex char '{c}'").toUInt64
  if i.hasNext then fromHex i.next acc' else acc'

def ClangId.ofString! (str : String) : ClangId :=
  fromHex str.iter.next.next 0

instance : FromJson ClangId where
  fromJson?
    | .str str => .ok (ClangId.ofString! str)
    | _ => .error "Expected a string"

instance : Repr ClangId := inferInstanceAs (Repr UInt64)
instance : BEq ClangId := inferInstanceAs (BEq UInt64)
instance : Hashable ClangId := inferInstanceAs (Hashable UInt64)

structure Loc where
  offset : Option Nat
  line : Option Nat
  col : Option Nat
  tokLen : Option Nat
deriving BEq, Hashable, Repr

def Loc.fromJson? (json : Json) : Except String (Loc × Option String) := do
  let loc ← Loc.mk <$> json.getObjValAs? _ "offset" <*> json.getObjValAs? _ "line" <*> json.getObjValAs? _ "col" <*> json.getObjValAs? _ "tokLen"
  let file ← json.getObjValAs? _ "file"
  return (loc, file)

structure RangePos where
  offset : Nat
  col : Nat
  tokLen : Nat
deriving BEq, Hashable, Repr

instance : FromJson RangePos where
  fromJson? v :=
    .mk <$> v.getObjValAs? _ "offset" <*> v.getObjValAs? _ "col" <*> v.getObjValAs? _ "tokLen"

structure Positioned where
  file : String
  loc : Option Loc
  begin : Option RangePos
  «end» : Option RangePos
deriving BEq, Hashable, Repr

def Positioned.fromJson? (file : String) (json : Json) : Except String Positioned := do
  let (loc, newFile) ← Loc.fromJson? (← json.getObjVal? "loc")
  let file := newFile.getD file
  let range ← json.getObjVal? "range"
  .mk file loc <$> (some <$> range.getObjValAs? _ "begin" <|> pure none)
               <*> (some <$> range.getObjValAs? _ "end" <|> pure none)

structure Typedef extends Positioned where
  name : String
  id : ClangId
  meaning : String -- the contents of .inner.[0].type.qualType
deriving BEq, Hashable, Repr


def Typedef.fromJson? (file : String) (json : Json) : Except String Typedef := do
    let pos ← Positioned.fromJson? file json
    Typedef.mk pos <$> json.getObjValAs? String "name" <*> json.getObjValAs? ClangId "id" <*> (← (← (← json.getObjVal? "inner").getArrVal? 0).getObjVal? "type").getObjValAs? String "qualType"

instance [BEq α] [Hashable α] [Repr α] [Repr β] : Repr (Std.HashMap α β) where
  reprPrec v p := Repr.addAppParen ("fromList " ++ repr v.toList ) p

structure TypeOcc where
  qualType : String
  typeAliasDeclId : Option ClangId := none
  desugaredQualType : Option String := none
deriving Repr, BEq, Hashable

instance : FromJson TypeOcc where
  fromJson? v :=
    let id := v.getObjValAs? ClangId "typeAliasDeclId" |>.toOption
    let desugared := v.getObjValAs? String "desugaredQualType" |>.toOption
    .mk <$> v.getObjValAs? String "qualType" <*> pure id <*> pure desugared

structure Param where
  name : Option String
  type : TypeOcc
deriving Repr

instance : FromJson Param where
  fromJson? v := do
    unless (← v.getObjVal? "kind") == "ParmVarDecl" do
      throw "Expected kind ParmVarDecl"
    let name := v.getObjValAs? String "name" |>.toOption
    .mk name <$> v.getObjValAs? TypeOcc "type"

structure FunctionDecl extends Positioned where
  name : String
  params : Array Param
  type : TypeOcc
deriving Repr

def FunctionDecl.fromJson? (file : String) (v : Json) : Except String FunctionDecl := do
    unless (← v.getObjVal? "kind") == "FunctionDecl" do
      throw "Expected kind FunctionDecl"
    let pos ← Positioned.fromJson? file v
    let params :=
      if let .ok (.arr stmts) := v.getObjVal? "inner" then
        let params := stmts.takeWhile fun (s : Json) => (s.getObjValAs? String "kind" |>.toOption |>.getD "") == "ParmVarDecl"
        params.mapM (FromJson.fromJson? (α := Param))
      else pure #[]
    .mk pos <$> v.getObjValAs? String "name" <*> params <*> v.getObjValAs? TypeOcc "type"

inductive TagUsed where | struct | union
deriving Repr

instance : FromJson TagUsed where
  fromJson?
    | .str "struct" => pure .struct
    | .str "union" => pure .union
    | _ => .error "expected 'struct' or 'union'"

structure Field where
  name : String
  type : TypeOcc
deriving Repr, BEq, Hashable

instance : FromJson Field where
  fromJson? v := do
    unless (← v.getObjVal? "kind") == "FieldDecl" do
      throw "Expected kind FieldDecl"
    .mk <$> v.getObjValAs? String "name" <*> v.getObjValAs? TypeOcc "type"

structure Record where
  tagUsed : TagUsed
  id : ClangId
  name : Option String
  previousDecl : Option ClangId
  fields : Option (Array Field)
deriving Repr

instance : FromJson Record where
  fromJson? v := do
    unless (← v.getObjVal? "kind") == "RecordDecl" do
      throw "Expected kind RecordDecl"
    .mk <$> v.getObjValAs? TagUsed "tagUsed" <*> v.getObjValAs? _ "id" <*> v.getObjValAs? _ "name" <*> v.getObjValAs? _ "previousDecl" <*> v.getObjValAs? _ "inner"

structure ClangEnv where
  allById : Std.HashMap ClangId String := {}
  /--
  A mapping from IDs to records. NB: for forward declarations, a given record may have multiple IDs,
  one for each declaration. To find a record based on an ID, first look it up here, then look up its
  name in `recordByName`, which tracks only the most informative version.
  -/
  records : Std.HashMap ClangId Record := {}
  recordsByName : Std.HashMap String Record := {}
  typedefs : Std.HashMap ClangId Typedef := {}
  typedefsByName : Std.HashMap String Typedef := {}
  functions : Std.HashMap String FunctionDecl := {}
deriving Repr, Inhabited

def ClangEnv.addRecord (env : ClangEnv) (record : Record) : ClangEnv :=
  let env := {env with records := env.records.insert record.id record}
  if let some name := record.name then
    {env with recordsByName := env.recordsByName.insert name record}
  else env

partial def process (ast : Json) : StateT String (StateT ClangEnv (Except String)) Unit := do
  try
    match ast with
    | .obj _ =>
      if let .ok kind := ast.getObjValAs? String "kind" then
        match kind with
        | "TranslationUnitDecl" =>
          let .ok (.arr stmts) := ast.getObjVal? "inner"
            | throw "Expected \"inner\" field in TranslationUnitDecl"
          stmts.forM process
        | "TypedefDecl" =>
          let typedef ← Typedef.fromJson? (← getThe String) ast
          modifyThe String fun _ => typedef.file
          modifyThe ClangEnv fun st => {st with typedefs := st.typedefs.insert typedef.id typedef}
          modifyThe ClangEnv fun st => {st with typedefsByName := st.typedefsByName.insert typedef.name typedef}
        | "FunctionDecl" =>
          let decl ← FunctionDecl.fromJson? (← getThe String) ast
          modifyThe String fun _ => decl.file
          modifyThe ClangEnv fun st => {st with functions := st.functions.insert decl.name decl}
        | "RecordDecl" =>
          let v ← FromJson.fromJson? ast
          modifyThe ClangEnv (·.addRecord v)
        | _ => pure ()
      else pure ()
    | _ => pure ()
  catch e =>
    dbg_trace e
    dbg_trace ast
    throw e

def llvmAST (file : System.FilePath) : IO ClangEnv := do
  match Json.parse (← IO.FS.readFile file) with
  | .error e => throw (IO.userError e)
  | .ok v =>
    match process v "" {} with
    | .error e => throw (IO.userError e)
    | .ok (((), _), env) => pure env


def timedAST (file : System.FilePath) := timeit "Reading AST" (llvmAST file)

initialize leanClangEnv : ClangEnv ← do
  let prog := "#include<lean/lean.h>"
  let child ← do
    let child ← IO.Process.spawn {
      cmd := "leanc",
      args := #["-Xclang", "-ast-dump=json", "-fsyntax-only", "-E", "-"],
      stdin := .piped,
      stdout := .piped,
      stderr := .piped
    }
    let (stdin, child) ← child.takeStdin
    stdin.putStrLn prog
    pure child

  let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait
  let stdout ← IO.ofExcept stdout.get

  if exitCode != 0 then
    throw (IO.userError s!"FAILURE {exitCode}\nStdout:\n{stdout}\nStderr:\n{stderr}")
  match Json.parse stdout with
  | .error e => throw <| IO.userError e
  | .ok v =>
    match process v "" {} with
    | .error e => throw <| IO.userError e
    | .ok (((), _), env) => pure env
