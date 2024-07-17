import Lake
open Lake DSL

require verso from git "https://github.com/leanprover/verso"@"main"

package "verso-manual" where
  -- add package configuration options here

lean_lib Manual where

def inputTextFile' (path : FilePath) : SpawnM (BuildJob FilePath) :=
  Job.async do (path, ·) <$> computeTrace (TextFilePath.mk path)

def figureDir : FilePath := "figures"
def figureOutDir : FilePath := "static/figures"

def ensureDir (dir : System.FilePath) : IO Unit := do
  if !(← dir.pathExists) then
    IO.FS.createDirAll dir
  if !(← dir.isDir) then
    throw (↑ s!"Not a directory: {dir}")


target figures : Array FilePath := do
  let files := (← figureDir.readDir).filterMap fun f =>
    match f.path.extension with
    | some "tex" => some f.path
    | _ => none
  let files := files.qsort (toString · < toString ·)
  let srcs ← BuildJob.collectArray (← liftM <| files.mapM inputTextFile')
  let traceFile := figureDir.join "lake.trace"
  liftM <| srcs.bindSync fun srcInfo depTrace => do
    buildUnlessUpToDate traceFile depTrace traceFile do
      for src in srcInfo do
        let some f := src.fileStem
          | continue
        proc { cmd := "lualatex", args := #[f], cwd := some figureDir} (quiet := true)
        proc { cmd := "lualatex", args := #[f], cwd := some figureDir} (quiet := true)
        proc { cmd := "lualatex", args := #[f], cwd := some figureDir} (quiet := true)
        proc { cmd := "lualatex", args := #[f], cwd := some figureDir} (quiet := true)
        proc { cmd := "pdftocairo", args := #["-svg", s!"{f}.pdf", s!"{f}.svg"], cwd := some figureDir} (quiet := true)

        ensureDir "static"
        ensureDir figureOutDir
        for fmt in ["pdf", "svg"] do
          IO.println s!"Format: {fmt}"
          let built := s!"{f}.{fmt}"
          IO.FS.withFile (figureDir.join built) .read fun h =>
            IO.FS.withFile (figureOutDir.join built) .write fun h' => do
              let mut buf ← h.read 1024
              while !buf.isEmpty do
                h'.write buf
                buf ← h.read 1024

    pure (srcInfo, depTrace)

@[default_target]
lean_exe "generate-manual" where
  extraDepTargets := #[`figures]
  root := `Main
