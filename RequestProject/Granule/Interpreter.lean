module

public import RequestProject.Granule.Parser
public import RequestProject.Granule.Eval

/-!
# The Granule interpreter driver

A port of the evaluation pipeline of `Language.Granule.Interpreter`:
literate (markdown) preprocessing, embedded `-- gr` flags, parsing, resolving
imports (relative to the current directory or the `StdLib` include path),
evaluating the definitions in order (`evalDefs`) and finally running the
entry point `main` (`evalAtEntryPoint`).
-/

@[expose] public section

namespace Granule

/-- Errors reported by the interpreter (`InterpreterError`). -/
inductive InterpreterError where
  | parseError (msg : String)
  | evalError (msg : String)
  | fatalError (msg : String)
  deriving Repr

def InterpreterError.format : InterpreterError → String
  | .parseError msg => "Parse error: \n" ++ msg ++ "\n"
  | .evalError msg => "Evaluation error: \n" ++ msg ++ "\n"
  | .fatalError msg => "Fatal error: \n" ++ msg ++ "\n"

/-- Results of the interpreter (`InterpreterResult`). -/
inductive InterpreterResult where
  | noEval
  | value (v : Term 0)

/-- Configuration (a small subset of the Haskell `Globals`/`GrConfig`). -/
structure Config where
  includePath : String := "StdLib"
  noEval : Bool := false
  entryPoint : String := "main"

/-- Extract fenced `granule` code blocks from a markdown file, keeping line
numbers (`unMarkdown` from `Language.Granule.Syntax.Preprocessor.Markdown`). -/
def unMarkdown (env : String) (src : String) : String :=
  let strip (s : String) : String := s.trimAscii.toString
  let isOpen (l : String) : Bool :=
    strip l == "~~~" ++ env || strip l == "~~~ " ++ env ||
    strip l == "```" ++ env || strip l == "``` " ++ env
  let rec go (inBlock : Option String) : List String → List String
    | [] => []
    | l :: ls =>
      match inBlock with
      | none =>
        if strip l == "~~~" ++ env || strip l == "~~~ " ++ env then "" :: go (some "~~~") ls
        else if strip l == "```" ++ env || strip l == "``` " ++ env then "" :: go (some "```") ls
        else "" :: go none ls
      | some fence =>
        if strip l == fence then "" :: go none ls
        else if isOpen l then "" :: go inBlock ls
        else l :: go inBlock ls
  "\n".intercalate (go none (src.splitOn "\n")) ++ "\n"

/-- Flags embedded in one of the first three non-blank lines, e.g. `-- gr --no-eval`. -/
def embeddedFlags (src : String) : List String :=
  let lines := ((src.splitOn "\n").filter fun l => !l.trimAscii.isEmpty).take 3
  lines.flatMap fun l =>
    let l := l.trimAscii.toString
    if l.startsWith "--" then
      let rest := (l.drop 2).trimAscii.toString
      if rest.startsWith "gr" then
        ((rest.drop 2).toString.splitOn " ").filter (· ≠ "")
      else []
    else []

/-- Parse a file and (transitively) the modules it imports. -/
partial def parseWithImports (cfg : Config) (file : String) (src : String) :
    ExceptT InterpreterError IO (AST × List Extension) := do
  let (ast, exts) ← match parseDefs file src with
    | .ok r => pure r
    | .error e => throw (.parseError e)
  let rec go (todo : List String) (done : List String) (acc : AST) (exts : List Extension) :
      ExceptT InterpreterError IO (AST × List Extension) := do
    match todo.filter (fun i => !done.contains i) with
    | [] => return (acc, exts)
    | i :: rest =>
      let local_ ← (System.FilePath.mk i).pathExists
      let path := if local_ then i else (System.FilePath.mk cfg.includePath / i).toString
      let src ← match ← (IO.FS.readFile path).toBaseIO with
        | .ok s => pure s
        | .error e => throw (InterpreterError.parseError s!"{path}: {e}")
      let (ast', exts') ← match parseDefs path src with
        | .ok r => pure r
        | .error e => throw (.parseError e)
      go (rest ++ ast'.imports) (i :: done)
        { acc with dataDecls := ast'.dataDecls ++ acc.dataDecls, defs := ast'.defs ++ acc.defs }
        (exts ++ exts')
  go ast.imports [] { ast with imports := [] } exts

open Eval in
/-- Evaluate the definitions in order (`evalDefs`). -/
def evalDefs (defs : List Def) : EvalM Unit := do
  for d in defs do
    let v ← evalIn d.toTerm
    let rt ← read
    let gs ← rt.globals.get
    if gs.contains d.name then
      if !d.name.contains '@' then
        evalError s!"Name clash: `{d.name}` was already in the context."
    else
      rt.globals.set (gs.insert d.name v)

open Eval in
/-- Evaluate a program at its entry point (`evalAtEntryPoint`). -/
def evalAtEntryPoint (entry : String) (ast : AST) (cbn : Bool) : IO (Option (Term 0)) := do
  let rt : Runtime := {
    globals := ← IO.mkRef (Std.HashMap.ofList builtins)
    dataDecls := ast.dataDecls
    cbn := cbn
    resources := ← IO.mkRef {}
    counter := ← IO.mkRef 0 }
  let act : EvalM (Option (Term 0)) := do
    evalDefs ast.defs
    match (← rt.globals.get)[entry]? with
    | none => return none
    | some v =>
      match v.unclose with
      | .pure e => return some (← evalIn e)
      | .effect f args => return some (← evalIn (← runEffect f args.toList))
      | .promote e => return some (← evalIn e)
      | .nec e => return some (← evalIn e)
      | _ => return some v
  act.run rt

/-- Run the interpreter on a source string (`Language.Granule.Interpreter.run`). -/
def run (cfg : Config) (file : String) (input : String) :
    IO (Except InterpreterError InterpreterResult) := do
  let input := if file.endsWith ".md" then unMarkdown "granule" input else input
  let cfg := if (embeddedFlags input).contains "--no-eval" then { cfg with noEval := true }
    else cfg
  match ← (parseWithImports cfg file input).run with
  | .error e => return .error e
  | .ok (ast, exts) =>
    if cfg.noEval then return .ok .noEval
    try
      match ← evalAtEntryPoint cfg.entryPoint ast (exts.contains .cbn) with
      | none => return .ok .noEval
      | some v => return .ok (.value v)
    catch e =>
      let msg := toString e
      let msg := if msg.startsWith runtimeErrorPrefix then (msg.drop runtimeErrorPrefix.length).toString
        else msg
      return .error (.evalError msg)

/-- Run a file. -/
def runFile (cfg : Config) (file : String) : IO (Except InterpreterError InterpreterResult) := do
  let src ← IO.FS.readFile file
  run cfg file src

end Granule

end
