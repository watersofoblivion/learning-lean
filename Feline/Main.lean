def bufsize: USize := 20 * 1024

partial def dump (input: IO.FS.Stream): IO Unit := do
  let buf ← input.read bufsize
  if buf.isEmpty
  then pure ()
  else
    let stdout ← IO.getStdout
    stdout.write buf
    dump input

def fileStream (fileName: System.FilePath): IO (Option IO.FS.Stream) := do
  let fileExists ← fileName.pathExists
  if not fileExists
  then
    let stderr ← IO.getStderr
    stderr.putStrLn s!"File {fileName} does not exist!"
    pure none
  else
    let handle ← IO.FS.Handle.mk fileName IO.FS.Mode.read
    pure (some (IO.FS.Stream.ofHandle handle))

def process (exitCode: UInt32) (args: List String): IO UInt32 := do
  match args with
    | [] => pure exitCode
    | "-" :: tl =>
      let stdin ← IO.getStdin
      dump stdin
      process exitCode tl
    | fileName :: tl =>
      let stream ← fileStream fileName
      match stream with
        | none => process 1 tl
        | some stream =>
          dump stream
          process exitCode tl

def main (args: List String) : IO UInt32 :=
  match args with
    | [] => process 0 ["-"]
    | args => process 0 args
