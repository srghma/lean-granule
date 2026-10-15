module

public import RequestProject.Granule.Interpreter

/-!
# Golden test runner

A port of the positive part of `interpreter/tests/Golden.hs`: every Granule
file in `examples`, `StdLib` and `frontend/tests/cases/positive` is run, and
the pretty-printed value of `main` is compared with the contents of the
accompanying `.output` file (files without an `.output` file must run without
error and produce no value, as in the Haskell test-suite).

Usage: `lake exe granule-test [DIR...]` (run from the repository root).
-/

@[expose] public section

open Granule

def isGranuleFile (p : System.FilePath) : Bool :=
  p.toString.endsWith ".gr" || p.toString.endsWith ".gr.md"

def collect (dir : String) : IO (Array String) := do
  if !(← System.FilePath.isDir dir) then return #[]
  let files ← System.FilePath.walkDir dir
  return (files.filter isGranuleFile |>.map (·.toString)).qsort (· < ·)

/-- Run one golden test, returning an error message on failure. -/
def runTest (file : String) : IO (Option String) := do
  let outFile := file ++ ".output"
  let expected ← if ← System.FilePath.pathExists outFile then
      some <$> IO.FS.readFile outFile else pure none
  -- silence the program's own output
  let buf ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let oldOut ← IO.setStdout (IO.FS.Stream.ofBuffer buf)
  let result ← try runFile {} file catch e => pure (.error (.fatalError (toString e)))
  let _ ← IO.setStdout oldOut
  let actual : Except String String := match result with
    | .ok (.value v) => .ok v.pretty
    | .ok .noEval => .ok ""
    | .error e => .error e.format
  match actual, expected with
  | .error e, _ => return some s!"error: {e}"
  | .ok act, some exp =>
    if act == exp then return none
    else return some s!"expected:\n{exp}\nactual:\n{act}"
  | .ok _, none => return none

def defaultDirs : List String := ["examples", "StdLib", "frontend/tests/cases/positive"]

def main (args : List String) : IO UInt32 := do
  let dirs := if args.isEmpty then defaultDirs else args
  let mut files : Array String := #[]
  for d in dirs do
    if d.endsWith ".gr" || d.endsWith ".gr.md" then files := files.push d
    else files := files ++ (← collect d)
  let mut failures : Array String := #[]
  for f in files do
    match ← runTest f with
    | none => IO.println s!"PASS {f}"
    | some msg =>
      IO.println s!"FAIL {f}\n{msg}"
      failures := failures.push f
  IO.println s!"\n{files.size - failures.size}/{files.size} tests passed"
  if failures.isEmpty then return 0
  IO.println "Failures:"
  for f in failures do IO.println s!"  {f}"
  return 1

end
