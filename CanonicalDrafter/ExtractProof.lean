import Lean
import Lake
import ExtractData

open System IO LeanDojo

/--
Read the proof string passed as `--proof="..."` from command-line arguments.
Throws if not exactly one `--proof=` flag is provided.
-/
def readProofArg (args : List String) : IO String := do
  let proofs := args.filter (·.startsWith "--proof=")
  match proofs with
  | [arg] =>
    let raw := (arg.drop "--proof=".length)
    let trimmed := raw.drop 1 |>.dropRight 1
    pure trimmed
  | _     =>
    throw (IO.userError "Usage: --proof=\"<proof tactics>\"")

/--
Extract the `haveDrafts` array from the JSON file at `jsonPath` and print it.
-/
def printHaveDrafts (jsonPath : FilePath) : IO Unit := do
  let contents ← IO.FS.readFile jsonPath
  -- parse into a Json structure
  let js ← match Lean.Json.parse contents with
    | Except.ok j   => pure j
    | Except.error e => throw (IO.userError s!"JSON parse error: {e}")
  let arrJson ← match js.getObjVal? "haveDrafts" with
    | Except.ok v   => pure v
    | Except.error e => throw (IO.userError s!"missing field haveDrafts: {e}")
  -- ensure it’s an array
  let arr ← match arrJson.getArr? with
    | Except.ok xs  => pure xs
    | Except.error e => throw (IO.userError s!"haveDrafts is not an array: {e}")
  -- now re-emit that array as JSON text
  IO.println s!"haveDrafts = {Lean.toJson arr}"

/--
Main entrypoint: reads the proof, wraps it in an `example` block,
invokes the existing `processFile` on a temporary file, and prints the drafts.
-/
unsafe def main (args : List String): IO Unit := do
  -- 1. Read the proof from args
  let proof ← readProofArg args

  -- 2. Create a temporary file under `tmp/`
  let cwd ← IO.currentDir
  let tmpDir := cwd / "tmp"
  let tmpFile := tmpDir / "ExtractProof.lean"
  -- ensure directory exists
  IO.FS.createDirAll tmpDir

  let fileContent :=
    proof.trim ++ "\n"

  IO.FS.writeFile tmpFile fileContent

  -- 4. Run the extractor on this file (writes JSON to .lake/build/ir/tmp/...)
  processFile tmpFile

  -- 5. Compute the path to the JSON output
  let jsonPath := FilePath.mk ".lake" / "build" / "ir" / tmpDir /
                  "ExtractProof.ast.json"

  -- 6. Read and print only the `haveDrafts` field
  printHaveDrafts jsonPath
