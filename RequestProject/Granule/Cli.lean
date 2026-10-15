module

public import RequestProject.Granule.Interpreter

/-!
# `granule` command line interface

`lake exe granule FILE...` runs each Granule file and prints the value of
`main` (like `gr` from the Haskell implementation, without type checking).
-/

@[expose] public section

open Granule

def main (args : List String) : IO UInt32 := do
  let mut status : UInt32 := 0
  for f in args do
    match ← runFile {} f with
    | .ok (.value v) => IO.println v.pretty
    | .ok .noEval => pure ()
    | .error e =>
      IO.eprint e.format
      status := 1
  return status

end
