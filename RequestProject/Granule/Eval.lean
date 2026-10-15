module

public import RequestProject.Granule.Scope
public import RequestProject.Granule.Pretty
public import Std.Sync.Channel
public import Std.Data.HashMap

/-!
# Granule interpreter

A port of `Language.Granule.Interpreter.Eval`.  Both evaluation strategies of
the Haskell interpreter are provided: the default call-by-value big-step
semantics (`evalCBV`) and the call-by-name semantics used with the `CBN`
language extension (`evalWHNF`, `evalCBNdeep`).

Evaluation works on closed terms `Term 0`.  Applying a function substitutes
closed values for the pattern variables (`Term.instantiate`), exactly as the
Haskell interpreter substitutes values for (freshened) variables.

Builtins are represented by partially applied primitives `Term.prim f args`;
once a primitive receives all its arguments its Lean implementation
(`applyPrim`) runs.  Suspended side effects (`PureWrapper` in Haskell) are
`Term.effect f args`, run by `runEffect`.
-/

@[expose] public section

namespace Granule

/-- `Fin.append` for functions out of `Fin`. -/
def finAppend {m n : Nat} {α : Type} (f : Fin m → α) (g : Fin n → α) : Fin (m + n) → α :=
  Fin.addCases f g

/-- One end of a bidirectional channel. -/
structure BChan where
  fwd : Std.Channel (Term 0)
  bwd : Std.Channel (Term 0)
  putbackFwd : IO.Ref (Option (Term 0))
  putbackBwd : IO.Ref (Option (Term 0))

def BChan.dual (c : BChan) : BChan := ⟨c.bwd, c.fwd, c.putbackBwd, c.putbackFwd⟩

/-- Runtime resources referred to by `Term.rt`. -/
inductive Resource where
  | handle (h : IO.FS.Handle) (peeked : IO.Ref (Option UInt8))
  | chan (c : BChan)
  | floatArray (a : IO.Ref (Array Float))
  | ref (r : IO.Ref (Term 0))

/-- The interpreter's environment. -/
structure Runtime where
  globals : IO.Ref (Std.HashMap String (Term 0))
  dataDecls : List DataDecl
  cbn : Bool
  resources : IO.Ref (Std.HashMap Nat Resource)
  counter : IO.Ref Nat

abbrev EvalM := ReaderT Runtime IO

instance {α : Type} : Inhabited (EvalM α) := ⟨fun _ => throw (IO.userError "")⟩

/-- Prefix of uncatchable runtime errors (Haskell `error`). -/
def runtimeErrorPrefix : String := "Granule runtime error: "

def evalError {α : Type} (msg : String) : EvalM α :=
  throw (IO.userError (runtimeErrorPrefix ++ msg))

def isRuntimeError (e : IO.Error) : Bool :=
  match e with
  | .userError msg => msg.startsWith runtimeErrorPrefix
  | _ => false

/-- Number of patterns in a pattern list. -/
def Pats.length {k : Nat} : Pats k → Nat
  | .nil => 0
  | .cons _ ps => ps.length + 1

namespace Eval

def unit : Term 0 := .constr "()" .nil
def pair (a b : Term 0) : Term 0 := .constr "," (.ofList [a, b])
def boolV (b : Bool) : Term 0 := .constr (if b then "True" else "False") .nil

/-- Allocate a runtime resource. -/
def newResource (r : Resource) : EvalM (Term 0) := do
  let rt ← read
  let i ← rt.counter.modifyGet fun i => (i, i + 1)
  rt.resources.modify (·.insert i r)
  return .rt i

def getResource (t : Term 0) : EvalM Resource := do
  match t.unclose with
  | .rt i =>
    match (← (← read).resources.get)[i]? with
    | some r => return r
    | none => evalError s!"unknown runtime resource {i}"
  | v => evalError s!"expected a runtime resource but got {v.pretty}"

def getChan (t : Term 0) : EvalM BChan := do
  match ← getResource t with
  | .chan c => return c
  | _ => evalError "expected a channel"

def newChan : IO BChan := do
  return ⟨← Std.Channel.new, ← Std.Channel.new, ← IO.mkRef none, ← IO.mkRef none⟩

def readChan (c : BChan) : IO (Term 0) := do
  match ← c.putbackBwd.modifyGet fun x => (x, none) with
  | some v => return v
  | none => c.bwd.sync.recv

def writeChan (c : BChan) (v : Term 0) : IO Unit := c.fwd.sync.send v

def putbackChan (c : BChan) (v : Term 0) : IO Unit := c.putbackBwd.set (some v)

/-- Arity of each primitive. -/
def primArity : String → Nat
  | "div" | "compose" | "scale" | "cap" | "stringAppend" | "stringCons" | "stringSnoc"
  | "openHandle" | "writeChar" | "send" | "gsend" | "uniqueBind" | "trustedBind" | "withBorrow"
  | "readFloatArray" | "readFloatArrayI" | "swapRef" | "with" | "call"
  | "forkReplicate" | "forkReplicateExactly" | "forkMulticast" => 2
  | "offer" | "writeFloatArray" | "writeFloatArrayI" => 3
  | "handle" | "handleGr" => 4
  | _ => 1

/-- Builtin names and their initial values. -/
def builtinNames : List String :=
  ["div", "use", "compose", "scale", "cap", "moveChar", "moveInt", "moveString", "drop@Int",
   "drop@Char", "drop@Float", "drop@String", "drop@FloatArray", "pure", "fromPure",
   "intToFloat", "showInt", "showFloat", "readInt", "toStdout", "toStderr", "openHandle",
   "readChar", "writeChar", "closeHandle", "showChar", "charToInt", "charFromInt",
   "stringAppend", "stringUncons", "stringCons", "stringUnsnoc", "stringSnoc", "isEOF",
   "forkLinear", "forkNonLinear", "forkReplicate", "forkReplicateExactly", "forkMulticast",
   "fork", "recv", "send", "selectLeft", "selectRight", "offer", "close", "grecv", "gsend",
   "gclose", "uniqueReturn", "uniqueBind", "reveal", "trustedBind", "withBorrow", "split",
   "join", "borrowPush", "borrowPull", "newFloatArray", "newFloatArrayI", "lengthFloatArrayI",
   "readFloatArrayI", "writeFloatArrayI", "lengthFloatArray", "readFloatArray",
   "writeFloatArray", "deleteFloatArray", "newRef", "swapRef", "freezeRef", "readRef", "with",
   "projL", "projR", "call", "handle", "handleGr"]

def builtins : List (String × Term 0) :=
  builtinNames.map (fun n => (n, Term.prim n .nil)) ++
  [("tick", .pure unit), ("throw", .effect "throw" .nil), ("fromStdin", .effect "fromStdin" .nil)]

/-- Is the term a value form (Haskell's `Val`)? -/
def isValue : Term 0 → Bool
  | .closed v => isValue v
  | .lam _ _ | .promote _ | .pure _ | .nec _ | .ref _ | .constr _ _ | .int _ | .float _
  | .char _ | .string _ | .pack _ _ _ _ _ | .tyAbs _ _ | .prim _ _ | .rt _ | .effect _ _
  | .freeImpure _ | .freeBind _ _ _ | .global _ => true
  | _ => false

/-- `isReducible` from the Haskell interpreter. -/
def isReducible : Term 0 → Bool
  | .closed v => isReducible v
  | .global _ => true
  | .hole => false
  | t => !isValue t

/-- `constructorApplicationSpine`. -/
def spine : Term 0 → Option (String × List (Term 0))
  | .closed v => spine v
  | .constr c vs => some (c, vs.toList)
  | .app f e => do
    let (c, args) ← spine f
    return (c, args ++ [e])
  | _ => none

/-- Binary operators (`evalBinOp`). -/
def evalBinOp (op : Operator) (v1 v2 : Term 0) : EvalM (Term 0) := do
  let fail {α : Type} : EvalM α := evalError s!"[{repr op}, {v1.pretty}, {v2.pretty}]"
  match op, v1.unclose, v2.unclose with
  | .plus, .int a, .int b => return .int (a + b)
  | .plus, .float a, .float b => return .float (a + b)
  | .times, .int a, .int b => return .int (a * b)
  | .times, .float a, .float b => return .float (a * b)
  | .div, .float a, .float b => return .float (a / b)
  | .minus, .int a, .int b => return .int (a - b)
  | .minus, .float a, .float b => return .float (a - b)
  | .eq, .int a, .int b => return boolV (a == b)
  | .eq, .char a, .char b => return boolV (a == b)
  | .eq, .float a, .float b => return boolV (a == b)
  | .eq, a, b => return boolV (a.pretty == b.pretty)
  | .notEq, .int a, .int b => return boolV (a != b)
  | .notEq, .float a, .float b => return boolV (a != b)
  | .lesserEq, .int a, .int b => return boolV (a ≤ b)
  | .lesserEq, .float a, .float b => return boolV (a ≤ b)
  | .lesser, .int a, .int b => return boolV (a < b)
  | .lesser, .float a, .float b => return boolV (a < b)
  | .greaterEq, .int a, .int b => return boolV (a ≥ b)
  | .greaterEq, .float a, .float b => return boolV (a ≥ b)
  | .greater, .int a, .int b => return boolV (a > b)
  | .greater, .float a, .float b => return boolV (a > b)
  | _, _, _ => fail


/-- Call-by-value pattern matching of a value (`pmatchCBV`); returns the
values for the pattern variables. -/
partial def matchCBV {k : Nat} (p : Pat k) (v : Term 0) : Option (Fin k → Term 0) :=
  match p, v.unclose with
  | .wild, _ => some Fin.elim0
  | .var _, _ => some fun _ => v
  | .constr c ps, .constr c' vs =>
    if c == c' && ps.length == vs.toList.length then matchPatsCBV ps vs.toList else none
  | .box p, .promote v' => matchCBV p v'
  | .int n, .int m => if n == m then some Fin.elim0 else none
  | .float n, .float m => if n == m then some Fin.elim0 else none
  | .char n, .char m => if n == m then some Fin.elim0 else none
  | _, _ => none
where
  matchPatsCBV {k : Nat} : Pats k → List (Term 0) → Option (Fin k → Term 0)
    | .nil, [] => some Fin.elim0
    | .cons p ps, v :: vs => do
      let f ← matchCBV p v
      let g ← matchPatsCBV ps vs
      return finAppend f g
    | _, _ => none

/-- A case alternative at top level. -/
structure Arm where
  k : Nat
  pat : Pat k
  body : Term (0 + k)

def armsToList : Arms 0 → List Arm
  | .nil => []
  | .cons p b rest => ⟨_, p, b⟩ :: armsToList rest

def varTerm1 : Term (0 + 1) := .var ⟨0, by omega⟩

/-- Weaken a body over a pattern under one extra outer binder. -/
def shiftUnder {k : Nat} (body : Term (0 + k)) : Term ((0 + 1) + k) :=
  body.rename (liftRen (fun i : Fin 0 => i.elim0) k)

/-- `\x -> e x` style wrappers built from Lean: `lam x. body` where body may
mention `x` as `varTerm1`. -/
def lam1 (body : Term (0 + 1)) : Term 0 := .lam (.var "x") body

/-! ## Derived operations (`push`, `pull`, `copyShape`, `drop`)

The Haskell type checker generates code for these; here we implement them
directly by inspecting the runtime value and the declared field types of the
data constructors. -/

/-- Field types of a data constructor and the type variables that are
parameters of the data type (as opposed to existentially bound ones). -/
def constrInfo (decls : List DataDecl) (c : String) : Option (List Ty × List String) := do
  let d ← decls.find? fun d => d.constrs.any (·.name == c)
  let dc ← d.constrs.find? (·.name == c)
  match dc with
  | .nonIndexed _ ps => return (ps, d.tyVars.map (·.1))
  | .indexed _ sch =>
    let params := (sch.ty.result.appArgs.filterMap fun
      | .var x => some x
      | _ => none)
    return (sch.ty.params, params)

def isPairTy : Ty → Option (Ty × Ty)
  | .app (.app (.con ",") a) b => some (a, b)
  | _ => none

/-- The name of the head type constructor of a type, if any. -/
def headName (t : Ty) : Option String :=
  match t.leftmost with
  | .con n => some n
  | _ => none

/-- The derived operation name for an operation at a type (`makeDerivedName`). -/
def makeDerivedName (op : String) (t : Ty) : String := op ++ "@" ++ t.leftmost.pretty

/-! ## The evaluator -/

mutual

/-- Look up a global (top-level definition or builtin). -/
partial def lookupGlobal (x : String) : EvalM (Term 0) := do
  match (← (← read).globals.get)[x]? with
  | some v => return v
  | none =>
    if ["push@", "pull@", "copyShape@", "drop@"].any (x.startsWith ·) then
      return .prim ("derived:" ++ x) .nil
    else
      throw (IO.userError s!"Variable '{x}' is undefined in context.")

/-- Apply a (partially applied) primitive to one more argument. -/
partial def applyPrimArg (f : String) (args : List (Term 0)) (v : Term 0) : EvalM (Term 0) := do
  let args := args ++ [v]
  let arity := if f.startsWith "derived:" then 1 else primArity f
  if args.length < arity then return .prim f (.ofList args)
  else applyPrim f args

/-- Apply a value to an (already evaluated) argument in call-by-value style. -/
partial def applyValue (f v : Term 0) : EvalM (Term 0) := do
  match f.unclose with
  | .prim g args => applyPrimArg g args.toList v
  | .lam p body =>
    match matchCBV p v with
    | some vals => evalIn (body.instantiate vals)
    | none => evalError s!"Runtime exception: Failed pattern match {p.pretty} against {v.pretty}"
  | .constr c vs => return .constr c (.ofList (vs.toList ++ [v]))
  | g => evalError s!"LHS of an application is not a function value {g.pretty}"

/-- Run a suspended side effect (`PureWrapper`), returning an expression. -/
partial def runEffect (f : String) (args : List (Term 0)) : EvalM (Term 0) := do
  match f, args with
  | "return", [o] => return o
  | "throw", [] => evalError "Granule `throw` exception raised, and not caught. Bye!"
  | "fromStdin", [] =>
    let out ← IO.getStdout
    out.putStr "> "; out.flush
    let line ← (← IO.getStdin).getLine
    let line := if line.endsWith "\n" then (line.dropEnd 1).toString else line
    return .string line
  | "toStdout", [s] =>
    match s.unclose with
    | .string s => let out ← IO.getStdout; out.putStr s; out.flush; return unit
    | _ => evalError "toStdout expects a string"
  | "toStderr", [s] =>
    match s.unclose with
    | .string s => (← IO.getStderr).putStr ("\x1b[31;1m" ++ s ++ "\x1b[0m"); return unit
    | _ => evalError "toStderr expects a string"
  | "openHandle", [m, s] =>
    let mode ← match m.unclose with
      | .constr "ReadMode" _ => pure IO.FS.Mode.read
      | .constr "WriteMode" _ => pure IO.FS.Mode.write
      | .constr "AppendMode" _ => pure IO.FS.Mode.append
      | .constr "ReadWriteMode" _ => pure IO.FS.Mode.readWrite
      | v => evalError s!"unknown mode {v.pretty}"
    match s.unclose with
    | .string path =>
      let h ← IO.FS.Handle.mk path mode
      newResource (.handle h (← IO.mkRef none))
    | v => evalError s!"Runtime exception: trying to open from a non string filename{v.pretty}"
  | "readChar", [h] =>
    match ← getResource h with
    | .handle hd peeked =>
      let c ← readUtf8Char hd peeked
      return pair h (.char c)
    | _ => evalError "Runtime exception: trying to get from a non handle value"
  | "writeChar", [h, c] =>
    match ← getResource h, c.unclose with
    | .handle hd _, .char ch => hd.putStr (String.singleton ch); return h
    | _, _ => evalError "Runtime exception: trying to put a non character value"
  | "closeHandle", [h] =>
    match ← getResource h with
    | .handle hd _ => hd.flush; return unit
    | _ => evalError "Runtime exception: trying to close a non handle value"
  | "isEOF", [h] =>
    match ← getResource h with
    | .handle hd peeked =>
      match ← peeked.get with
      | some _ => return pair h (boolV false)
      | none =>
        let bs ← hd.read 1
        if bs.size == 0 then return pair h (boolV true)
        else peeked.set (some bs[0]!); return pair h (boolV false)
    | _ => evalError "isEOF expects a handle"
  | "fork", [fn] =>
    let c ← newChan
    let rt ← read
    let r ← newResource (.chan c)
    let _ ← IO.asTask (prio := .dedicated) ((evalIn (.app fn (.promote r))).run rt)
    let d ← newResource (.chan c.dual)
    return .promote d
  | "grecv", [ch] =>
    let c ← getChan ch
    let x ← readChan c
    return pair x ch
  | "gsend", [ch, v] =>
    let c ← getChan ch
    writeChan c v
    return ch
  | "gclose", [_] => return unit
  | _, _ => evalError s!"unknown effect {f}"

/-- Read one UTF-8 encoded character from a handle. -/
partial def readUtf8Char (h : IO.FS.Handle) (peeked : IO.Ref (Option UInt8)) : EvalM Char := do
  let nextByte : EvalM UInt8 := do
    match ← peeked.modifyGet fun p => (p, none) with
    | some b => return b
    | none =>
      let bs ← h.read 1
      if bs.size == 0 then throw (IO.userError "end of file") else return bs[0]!
  let b0 ← nextByte
  let n0 := b0.toNat
  if n0 < 0x80 then return Char.ofNat n0
  let (len, init) :=
    if n0 &&& 0xE0 == 0xC0 then (1, n0 &&& 0x1F)
    else if n0 &&& 0xF0 == 0xE0 then (2, n0 &&& 0x0F)
    else (3, n0 &&& 0x07)
  let mut code := init
  for _ in [0:len] do
    let b ← nextByte
    code := code * 64 + (b.toNat &&& 0x3F)
  return Char.ofNat code

/-- Run the side effects of a diamond value (`isDiaConstr`). -/
partial def runDiamond (v : Term 0) : EvalM (Option (Term 0)) := do
  match v.unclose with
  | .pure e => return some e
  | .effect f args => return some (← runEffect f args.toList)
  | _ => return none

/-- Fork a thread evaluating `f arg`. -/
partial def forkEval (f arg : Term 0) : EvalM Unit := do
  let rt ← read
  let _ ← IO.asTask (prio := .dedicated) ((evalIn (.app f arg)).run rt)
  return ()

/-- Convert a Granule `N n` value into a natural number. -/
partial def natToInt (v : Term 0) : EvalM Nat := do
  match v.unclose with
  | .constr "Z" .nil => return 0
  | .constr "S" (.cons w .nil) => return (← natToInt w) + 1
  | k => evalError s!"Bug in Granule. Trying to convert a N but got value {k.pretty}"

/-- The implementations of the primitives, given all their arguments. -/
partial def applyPrim (f : String) (args : List (Term 0)) : EvalM (Term 0) := do
  let args' := args.map Term.unclose
  match f, args' with
  | "div", [.int a, .int b] => return .int (Int.fdiv a b)
  | "use", [v] => return .promote v
  | "compose", [g, f] =>
    return lam1 (.app (.ofClosed g) (.app (.ofClosed f) varTerm1))
  | "scale", [.float n, .promote m] =>
    match m.unclose with
    | .float m => return .float (n * m)
    | _ => evalError "scale"
  | "cap", [.constr "Console" _, _] => return .prim "cap:Console" .nil
  | "cap", [.constr "TimeDate" _, _] => return .prim "cap:TimeDate" .nil
  | "cap:Console", [.string s] =>
    let out ← IO.getStdout; out.putStr s; out.flush; return unit
  | "cap:TimeDate", [_] => return .string s!"{← IO.monoMsNow}"
  | "moveChar", [v@(.char _)] => return .promote v
  | "moveInt", [v@(.int _)] => return .promote v
  | "moveString", [v@(.string _)] => return .promote v
  | "drop@Int", [_] | "drop@Char", [_] | "drop@Float", [_] | "drop@String", [_]
  | "drop@FloatArray", [_] => return unit
  | "pure", [v] => return .pure v
  | "fromPure", [.pure e] => return e
  | "intToFloat", [.int n] => return .float (Float.ofInt n)
  | "showInt", [.int n] => return .string (toString n)
  | "showFloat", [.float x] => return .string (HaskellShow.showDouble x)
  | "readInt", [.string s] =>
    if s.isEmpty then return .int 0
    else match s.trimAscii.toString.toInt? with
      | some n => return .int n
      | none => evalError "Prelude.read: no parse"
  | "toStdout", [s] => return .effect "toStdout" (.ofList [s])
  | "toStderr", [s] => return .effect "toStderr" (.ofList [s])
  | "openHandle", [m, s] => return .effect "openHandle" (.ofList [m, s])
  | "readChar", [h] => return .effect "readChar" (.ofList [h])
  | "writeChar", [h, c] => return .effect "writeChar" (.ofList [h, c])
  | "closeHandle", [h] => return .effect "closeHandle" (.ofList [h])
  | "isEOF", [h] => return .effect "isEOF" (.ofList [h])
  | "showChar", [.char c] => return .string (String.singleton c)
  | "charToInt", [.char c] => return .int c.toNat
  | "charFromInt", [.int n] => return .char (Char.ofNat n.toNat)
  | "stringAppend", [.string s, .string t] => return .string (s ++ t)
  | "stringUncons", [.string s] =>
    match s.toList with
    | c :: cs => return .constr "Just" (.ofList [pair (.char c) (.string (String.ofList cs))])
    | [] => return .constr "Nothing" .nil
  | "stringCons", [.char c, .string s] => return .string (String.singleton c ++ s)
  | "stringUnsnoc", [.string s] =>
    match s.toList.getLast? with
    | some c =>
      return .constr "Just" (.ofList [pair (.string (String.ofList s.toList.dropLast)) (.char c)])
    | none => return .constr "Nothing" .nil
  | "stringSnoc", [.string s, .char c] => return .string (s.push c)
  | "forkLinear", [fn@(.lam _ _)] =>
    let c ← newChan
    let r ← newResource (.chan c)
    forkEval fn r
    newResource (.chan c.dual)
  | "forkNonLinear", [fn@(.lam _ _)] =>
    let c ← newChan
    let r ← newResource (.chan c)
    forkEval fn (.promote r)
    return .promote (← newResource (.chan c.dual))
  | "forkReplicate", [.promote fn, n] => forkReplicateCore true fn n
  | "forkReplicateExactly", [.promote fn, n] => forkReplicateCore false fn n
  | "forkMulticast", [fn@(.lam _ _), n] =>
    let initChan ← newChan
    let initR ← newResource (.chan initChan.dual)
    forkEval fn initR
    let k ← natToInt n
    let receivers ← (List.range k).mapM fun _ => newChan
    let rt ← read
    -- forwarder: a value read from the broadcaster goes to every receiver
    let forward : IO Unit := do
      let e ← readChan initChan
      match e.unclose with
      | .promote v => for r in receivers do writeChan r v
      | _ => throw (IO.userError "Bug in Granule. Multicast forwarder got non-boxed value")
    let _ ← IO.asTask (prio := .dedicated) forward
    let _ := rt
    buildVec (← receivers.mapM fun r => newResource (.chan r.dual)) id
  | "fork", [fn] => return .effect "fork" (.ofList [fn])
  | "recv", [ch] =>
    let c ← getChan ch
    let x ← readChan c
    return pair x ch
  | "send", [ch, v] =>
    let c ← getChan ch
    writeChan c v
    return ch
  | "selectLeft", [ch] =>
    writeChan (← getChan ch) (.constr "LeftTag" .nil); return ch
  | "selectRight", [ch] =>
    writeChan (← getChan ch) (.constr "RightTag" .nil); return ch
  | "offer", [fl, fr, ch] =>
    let c ← getChan ch
    match (← readChan c).unclose with
    | .constr "LeftTag" _ => evalIn (.app fl ch)
    | .constr "RightTag" _ => evalIn (.app fr ch)
    | x => evalError s!"Bug in Granule. Offer got tag: {x.pretty}"
  | "close", [_] => return unit
  | "grecv", [ch] => return .effect "grecv" (.ofList [ch])
  | "gsend", [ch, v] => return .effect "gsend" (.ofList [ch, v])
  | "gclose", [ch] => return .effect "gclose" (.ofList [ch])
  | "uniqueReturn", [.nec v] =>
    match ← resourceOf v with
    | some (.floatArray a) =>
      let copy ← IO.mkRef (← a.get)
      return .promote (← newResource (.floatArray copy))
    | _ => return .promote v
  | "uniqueBind", [fn, .promote v] =>
    match ← resourceOf v with
    | some (.floatArray a) =>
      let copy ← IO.mkRef (← a.get)
      let r ← newResource (.floatArray copy)
      evalIn (.app fn (packUnique (.nec r) "FloatArray"))
    | some (.ref r) =>
      let copy ← IO.mkRef (← r.get)
      let r' ← newResource (.ref copy)
      evalIn (.app fn (packUnique (.nec r') "Ref"))
    | _ => evalIn (.app fn (.nec v))
  | "reveal", [.nec v] => return .promote v
  | "trustedBind", [fn, .promote v] =>
    match ← resourceOf v with
    | some (.floatArray a) =>
      let copy ← IO.mkRef (← a.get)
      let r ← newResource (.floatArray copy)
      evalIn (.app fn (.nec r))
    | _ => evalIn (.app fn (.nec v))
  | "withBorrow", [fn, .nec v] =>
    match (← evalIn (.app fn (.ref v))).unclose with
    | .ref v' => return .nec v'
    | r => evalError s!"withBorrow: expected a borrowed value but got {r.pretty}"
  | "split", [v] => return pair v v
  | "join", [.constr "," vs] =>
    match vs.toList.map Term.unclose with
    | [.ref x, .ref _] => return .ref x
    | _ => evalError "Bug in Granule. Can't join unborrowed types"
  | "borrowPush", [.ref p] =>
    match p.unclose with
    | .constr "," vs =>
      match vs.toList with
      | [x, y] => return pair (.ref x) (.ref y)
      | _ => evalError "borrowPush"
    | _ => evalError "Bug in Granule. Can't push through an unborrowed"
  | "borrowPush", [.nec p] =>
    match p.unclose with
    | .constr "," vs =>
      match vs.toList with
      | [x, y] => return pair (.nec x) (.nec y)
      | _ => evalError "borrowPush"
    | _ => evalError "Bug in Granule. Can't push through an unborrowed"
  | "borrowPull", [.constr "," vs] =>
    match vs.toList.map Term.unclose with
    | [.ref x, .ref y] => return .ref (pair x y)
    | [.nec x, .nec y] => return .nec (pair x y)
    | _ => evalError "Bug in Granule. Can't pull through an unborrowed"
  | "newFloatArray", [.int n] =>
    let a ← IO.mkRef (Array.replicate n.toNat (0 : Float))
    let r ← newResource (.floatArray a)
    return packUnique (.nec r) "FloatArray"
  | "newFloatArrayI", [.int n] =>
    let a ← IO.mkRef (Array.replicate n.toNat (0 : Float))
    newResource (.floatArray a)
  | "lengthFloatArrayI", [arr] =>
    let a ← floatArrayOf arr
    return pair (.promote (.int (← a.get).size)) arr
  | "lengthFloatArray", [w] =>
    let (inner, wrap) ← unwrapBorrow w
    let a ← floatArrayOf inner
    return pair (.promote (.int (← a.get).size)) (wrap inner)
  | "readFloatArrayI", [arr, .int i] =>
    let a ← floatArrayOf arr
    return pair (.float ((← a.get).getD i.toNat 0)) arr
  | "readFloatArray", [w, .int i] =>
    let (inner, wrap) ← unwrapBorrow w
    let a ← floatArrayOf inner
    return pair (.float ((← a.get).getD i.toNat 0)) (wrap inner)
  | "writeFloatArrayI", [arr, .int i, .float x] =>
    let a ← floatArrayOf arr
    a.modify (·.setIfInBounds i.toNat x)
    return arr
  | "writeFloatArray", [w, .int i, .float x] =>
    let (inner, wrap) ← unwrapBorrow w
    let a ← floatArrayOf inner
    a.modify (·.setIfInBounds i.toNat x)
    return wrap inner
  | "deleteFloatArray", [.nec arr] =>
    let _ ← floatArrayOf arr
    return unit
  | "newRef", [v] =>
    let r ← newResource (.ref (← IO.mkRef v))
    return packUnique (.nec r) "Ref"
  | "swapRef", [w, v] =>
    let (inner, wrap) ← unwrapBorrow w
    match ← getResource inner with
    | .ref r =>
      let old ← r.get
      r.set v
      return pair old (wrap inner)
    | _ => evalError "Runtime exception: trying to swap a non-reference value"
  | "readRef", [w] =>
    let (inner, wrap) ← unwrapBorrow w
    match ← getResource inner with
    | .ref r => return pair (← r.get) (wrap inner)
    | _ => evalError "Runtime exception: trying to read a non-reference value"
  | "freezeRef", [.nec inner] =>
    match ← getResource inner with
    | .ref r => r.get
    | _ => evalError "freezeRef"
  | "with", [v, w] => return .constr "&" (.ofList [v, w])
  | "projL", [.constr "&" vs] => return vs.toList.headD unit
  | "projR", [.constr "&" vs] => return vs.toList.getLastD unit
  | "call", [op, inp] =>
    -- call op x = Impure (op x (\o -> Pure o))
    return .freeImpure (.app (.app op inp) (.promote (.prim "pureReturn" .nil)))
  | "pureReturn", [o] => return .effect "return" (.ofList [o])
  | "handle", [fmap, alg, ret, comp] | "handleGr", [fmap, alg, ret, comp] =>
    handlePrim fmap alg ret comp
  | g, [v] =>
    if g.startsWith "derived:" then derived ((g.drop 8).toString) v
    else evalError s!"Bad application of primitive {f} to {", ".intercalate (args.map Term.pretty)}"
  | _, _ =>
    evalError s!"Bad application of primitive {f} to {", ".intercalate (args.map Term.pretty)}"

/-- Build a `Vec n` value of channels. -/
partial def buildVec (cs : List (Term 0)) (wrap : Term 0 → Term 0) : EvalM (Term 0) :=
  return cs.foldr (fun c acc => .constr "Cons" (.ofList [wrap c, acc])) (.constr "Nil" .nil)

partial def forkReplicateCore (boxed : Bool) (fn n : Term 0) : EvalM (Term 0) := do
  let k ← natToInt n
  let chans ← (List.range k).mapM fun _ => newChan
  for c in chans do
    let r ← newResource (.chan c)
    let rt ← read
    let waiter : IO Unit := do
      let x ← readChan c
      putbackChan c x
      let _ ← IO.asTask (prio := .dedicated) ((evalIn (.app fn r)).run rt)
    let _ ← IO.asTask (prio := .dedicated) waiter
  let ends ← chans.mapM fun c => newResource (.chan c.dual)
  buildVec ends (fun c => if boxed then .promote c else c)

/-- The resource behind a value, if it is a runtime resource. -/
partial def resourceOf (v : Term 0) : EvalM (Option Resource) := do
  match v.unclose with
  | .rt _ => return some (← getResource v)
  | _ => return none

partial def floatArrayOf (v : Term 0) : EvalM (IO.Ref (Array Float)) := do
  match ← getResource v with
  | .floatArray a => return a
  | _ => evalError "Runtime exception: expected an array value"

/-- Unwrap a unique (`*`) or borrowed (`&`) wrapper. -/
partial def unwrapBorrow (w : Term 0) : EvalM (Term 0 × (Term 0 → Term 0)) := do
  match w.unclose with
  | .nec x => return (x, Term.nec)
  | .ref x => return (x, Term.ref)
  | v => evalError s!"Runtime exception: expected a unique or borrowed value, got {v.pretty}"

/-- `pack <id, v> as exists {id : Name} . *T` for fresh unique resources. -/
partial def packUnique (v : Term 0) (tyName : String) : Term 0 :=
  .pack (.con "Name") v "id" (.con "Name") (.borrow (.con "Star") (.con tyName))

/-- Effect handlers (`handlePrim`): the catamorphism of the free monad. -/
partial def handlePrim (fmap alg ret comp : Term 0) : EvalM (Term 0) := do
  let fmapFun ← match fmap.unclose with
    | .promote inner =>
      match inner.unclose with
      | .tyAbs _ fmapInner => evalIn fmapInner
      | t => evalError s!"Internal bug: expecting a promoted function as first input to 'handle', got {t.pretty}"
    | t => evalError s!"Internal bug: expecting a promoted function as first input to 'handle', got {t.pretty}"
  match comp.unclose with
  | .effect f args =>
    let e ← runEffect f args.toList
    let v ← evalIn e
    evalIn (.app ret v)
  | .pure e =>
    let v ← evalIn e
    evalIn (.app ret v)
  | .freeImpure e =>
    let contVal ← evalIn e
    match alg.unclose with
    | .promote alg0 =>
      match (← evalIn alg0).unclose with
      | .tyAbs _ algInner =>
        let algFun ← evalIn algInner
        let handler : Term 0 :=
          .app (.app (.app (.global "handle") fmap) alg) ret
        evalIn (.app algFun (.app (.app fmapFun (.promote handler)) contVal))
      | a => evalError s!"Internal bug: handle expecting algebra argument to be a function, got {a.pretty}"
    | a => evalError s!"Internal bug: handle expecting algebra argument in a box, got {a.pretty}"
  | .freeBind v p rest =>
    let k : Term 0 := lam1 (.letDiamond p varTerm1 (shiftUnder rest))
    evalIn (.app (.app (.app (.app (.global "handle") fmap) alg) ret)
      (.freeImpure (.app (.app fmapFun (.promote k)) v)))
  | r => evalError s!"Interal bug: handle expecting a free monad but got {r.pretty}"

/-- Derived operations at runtime. -/
partial def derived (name : String) (v : Term 0) : EvalM (Term 0) := do
  let decls := (← read).dataDecls
  match name.splitOn "@" with
  | ["drop", _] => return unit
  | ["copyShape", _] => return pair (← shapeOf decls v) v
  | ["push", _] =>
    match v.unclose with
    | .promote x => pushValue decls x
    | x => evalError s!"push: expected a boxed value, got {x.pretty}"
  | ["pull", _] => pullValue v
  | _ => evalError s!"unknown derived operation {name}"

partial def shapeOf (decls : List DataDecl) (v : Term 0) : EvalM (Term 0) := do
  match v.unclose with
  | .constr "," vs =>
    match vs.toList with
    | [a, b] => return pair (← shapeOf decls a) (← shapeOf decls b)
    | _ => return v
  | .constr "()" _ => return unit
  | .constr c vs =>
    match constrInfo decls c with
    | some (tys, _) =>
      let args ← (tys.zip vs.toList).mapM fun (t, a) => shapeField decls t a
      return .constr c (.ofList args)
    | none => return unit
  | _ => return unit

partial def shapeField (decls : List DataDecl) (t : Ty) (a : Term 0) : EvalM (Term 0) := do
  match t with
  | .var _ => return unit
  | _ =>
    match isPairTy t with
    | some (t1, t2) =>
      match a.unclose with
      | .constr "," vs =>
        match vs.toList with
        | [x, y] => return pair (← shapeField decls t1 x) (← shapeField decls t2 y)
        | _ => return a
      | _ => return a
    | none =>
      match headName t with
      | some "Int" | some "Char" | some "Float" | some "String" => return a
      | some "()" => return unit
      | _ => shapeOf decls a

partial def pushValue (decls : List DataDecl) (x : Term 0) : EvalM (Term 0) := do
  match x.unclose with
  | .constr "," vs =>
    match vs.toList with
    | [a, b] => return pair (.promote a) (.promote b)
    | _ => evalError "push: malformed pair"
  | .constr "()" _ => return unit
  | .constr c vs =>
    match constrInfo decls c with
    | some (tys, params) =>
      let args ← (tys.zip vs.toList).mapM fun (t, a) => pushField decls params t a
      return .constr c (.ofList args)
    | none => evalError s!"Cannot push derive for constructor {c}"
  | y => evalError s!"push: unexpected value {y.pretty}"

partial def pushField (decls : List DataDecl) (params : List String) (t : Ty) (a : Term 0) :
    EvalM (Term 0) := do
  match t with
  | .var n => return if params.contains n then .promote a else a
  | _ =>
    match isPairTy t with
    | some _ => pushValue decls a
    | none =>
      match headName t with
      | some "()" => return unit
      | _ => pushValue decls a

partial def pullValue (v : Term 0) : EvalM (Term 0) := do
  match v.unclose with
  | .constr c vs =>
    let args ← vs.toList.mapM fun a =>
      match a.unclose with
      | .promote y => pure y
      | y => pullValue y >>= fun r =>
        match r.unclose with
        | .promote z => pure z
        | _ => pure y
    return .promote (.constr c (.ofList args))
  | y => evalError s!"pull: unexpected value {y.pretty}"

-- ### Call-by-value

/-- Call-by-value big-step evaluation (`evalInCBV`). -/
partial def evalCBV (t : Term 0) : EvalM (Term 0) := do
  match t with
  | .closed v => evalCBV v
  | .app e1 e2 =>
    let v1 ← evalCBV e1
    match v1.unclose with
    | .prim g args =>
      let v2 ← evalCBV e2
      applyPrimArg g args.toList v2
    | .lam p body =>
      let v2 ← evalCBV e2
      match ← matchOne p body v2 with
      | some e3 => evalCBV e3
      | none =>
        evalError s!"Runtime exception: Failed pattern match {p.pretty} against {v2.pretty} in application"
    | .constr c vs =>
      let v2 ← evalCBV e2
      return .constr c (.ofList (vs.toList ++ [v2]))
    | v => evalError v.pretty
  | .appTy (.global n) ty =>
    if ["push", "pull", "copyShape", "drop"].contains n then
      evalCBV (.global (makeDerivedName n ty))
    else evalAppTy (.global n)
  | .appTy e _ => evalAppTy e
  | .binop op e1 e2 =>
    let v1 ← evalCBV e1
    let v2 ← evalCBV e2
    evalBinOp op v1 v2
  | .letDiamond p e1 e2 =>
    let v1 ← evalCBV e1
    match ← runDiamond v1 with
    | some eInner =>
      let v1' ← evalCBV eInner
      match ← matchOne p e2 v1' with
      | some e2' => evalCBV e2'
      | none => evalError s!"Runtime exception: Failed pattern match {p.pretty} in let"
    | none =>
      match v1.unclose with
      | .freeImpure eInner =>
        let v1' ← evalCBV eInner
        return .freeBind v1' p e2
      | other =>
        throw (IO.userError s!"Runtime exception: Expecting a diamonad value but got: {other.pretty}")
  | .tryCatch e1 p e2 e3 =>
    let v1 ← evalCBV e1
    match v1.unclose with
    | .pure _ | .effect _ _ =>
      tryCatch
        (do
          let some eInner ← runDiamond v1 | evalError "impossible"
          let e1' ← evalCBV eInner
          match ← matchOne (.box p) e2 e1' with
          | some e2' => evalCBV e2'
          | none => evalError s!"Runtime exception: Failed pattern match {p.pretty} in try")
        (fun err => if isRuntimeError err then throw err else evalCBV e3)
    | other =>
      throw (IO.userError s!"Runtime exception: Expecting a diamond value but got: {other.pretty}")
  | .unpack _ x e1 e2 =>
    let v1 ← evalCBV e1
    match v1.unclose with
    | .pack _ eInner _ _ _ =>
      let v ← evalCBV eInner
      match ← matchOne (.var x) e2 v with
      | some e2' => evalCBV e2'
      | none => evalError "Runtime exception: Failed pattern match in unpack"
    | other =>
      throw (IO.userError s!"Runtime exception: Expecting a pack value but got: {other.pretty} ({x})")
  | .global x => lookupGlobal x
  | .promote e =>
    if (← read).cbn then return .promote e
    else return .promote (← evalCBV e)
  | .nec e =>
    if (← read).cbn then return .nec e
    else return .nec (← evalCBV e)
  | .case e arms =>
    let v ← evalCBV e
    match ← pmatch (armsToList arms) v with
    | some body => evalCBV body
    | none => evalError s!"Incomplete pattern match:\n  cases: ...\n  expr: {v.pretty}"
  | .hole => evalError "Trying to evaluate a hole, which should not have passed the type checker."
  | v => return v

partial def evalAppTy (e : Term 0) : EvalM (Term 0) := do
  let v ← evalCBV e
  match v.unclose with
  | .tyAbs (.inl _) inner => evalCBV inner
  | _ => evalError s!"Bug: LHS of a type application is not a type abstraction: {v.pretty}"

-- ### Pattern matching

/-- Pattern matching dispatch (`pmatch`). -/
partial def pmatch (arms : List Arm) (e : Term 0) : EvalM (Option (Term 0)) := do
  if (← read).cbn then pmatchCBN arms e
  else
    match arms with
    | [] => return none
    | a :: rest =>
      match matchCBV a.pat e with
      | some vals => return some (a.body.instantiate vals)
      | none => pmatch rest e

/-- Single-pattern match (used for applications, lets, unpacks). -/
partial def matchOne {k : Nat} (p : Pat k) (body : Term (0 + k)) (e : Term 0) :
    EvalM (Option (Term 0)) :=
  pmatch [⟨k, p, body⟩] e

-- ### Call-by-name

/-- Call-by-name pattern matching (`pmatchCBN`). -/
partial def pmatchCBN (arms : List Arm) (eg : Term 0) : EvalM (Option (Term 0)) := do
  match arms with
  | [] => return none
  | a :: rest =>
    let (res, eg') ← matchCBN a.pat eg
    match res with
    | some vals => return some (a.body.instantiate vals)
    | none => pmatchCBN rest eg'

/-- Match one pattern call-by-name; also returns the (possibly reduced)
scrutinee for use by subsequent alternatives. -/
partial def matchCBN {k : Nat} (p : Pat k) (eg : Term 0) :
    EvalM (Option (Fin k → Term 0) × Term 0) := do
  match p with
  | .wild => return (some Fin.elim0, eg)
  | .var _ => return (some fun _ => eg, eg)
  | .box q =>
    match eg.unclose with
    | .promote eg' =>
      let (r, _) ← matchCBN q eg'
      return (r, eg)
    | _ =>
      if isReducible eg then
        let eg' ← evalWHNF eg
        matchCBN (.box q) eg'
      else return (none, eg)
  | .constr c ps =>
    match spine eg with
    | none =>
      let eg' ← evalWHNF eg
      matchCBN (.constr c ps) eg'
    | some (c', args) =>
      if c == c' && ps.length == args.length then
        let r ← matchPatsCBN ps args
        return (r, eg)
      else return (none, eg)
  | .int n =>
    match eg.unclose with
    | .int m => if n == m then return (some Fin.elim0, eg) else return (none, eg)
    | _ => literalFallback (.int n) eg
  | .float n =>
    match eg.unclose with
    | .float m => if n == m then return (some Fin.elim0, eg) else return (none, eg)
    | _ => literalFallback (.float n) eg
  | .char n =>
    match eg.unclose with
    | .char m => if n == m then return (some Fin.elim0, eg) else return (none, eg)
    | _ => literalFallback (.char n) eg

partial def literalFallback {k : Nat} (p : Pat k) (eg : Term 0) :
    EvalM (Option (Fin k → Term 0) × Term 0) := do
  if isReducible eg then
    let eg' ← evalWHNF eg
    matchCBN p eg'
  else return (none, eg)

partial def matchPatsCBN {k : Nat} (ps : Pats k) (args : List (Term 0)) :
    EvalM (Option (Fin k → Term 0)) := do
  match ps, args with
  | .nil, [] => return some Fin.elim0
  | .cons q qs, a :: as =>
    let (r, _) ← matchCBN q a
    match r with
    | none => return none
    | some f =>
      match ← matchPatsCBN qs as with
      | some g => return some (finAppend f g)
      | none => return none
  | _, _ => return none

/-- Evaluation to weak head normal form (`evalInWHNF`). -/
partial def evalWHNF (t : Term 0) : EvalM (Term 0) := do
  match t with
  | .closed v => evalWHNF v
  | .app e1 e2 =>
    let v1 ← evalWHNF e1
    match v1.unclose with
    | .prim g args =>
      let v2 ← evalIn e2
      applyPrimArg g args.toList v2
    | .lam p body =>
      match ← pmatchCBN [⟨_, p, body⟩] e2 with
      | some e3 => return e3
      | none => evalError s!"Runtime exception: Failed pattern match {p.pretty} in application"
    | .constr _ _ => return .app v1 e2
    | v => evalError s!"LHS of an application is not a function value {v.pretty}"
  | .appTy (.global n) ty =>
    if ["push", "pull", "copyShape", "drop"].contains n then
      evalWHNF (.global (makeDerivedName n ty))
    else whnfAppTy (.global n)
  | .appTy e _ => whnfAppTy e
  | .binop op e1 e2 =>
    let v1 ← evalIn e1
    let v2 ← evalIn e2
    evalBinOp op v1 v2
  | .letDiamond p e1 e2 =>
    let v1 ← evalWHNF e1
    match ← runDiamond v1 with
    | some eInner =>
      let v1' ← evalWHNF eInner
      match ← pmatch [⟨_, p, e2⟩] v1' with
      | some e2' => evalWHNF e2'
      | none => evalError s!"Runtime exception: Failed pattern match {p.pretty} in let"
    | none =>
      throw (IO.userError s!"Runtime exception: Expecting a diamond value but got: {v1.pretty}")
  | .global x => lookupGlobal x
  | .case e arms =>
    match ← pmatchCBN (armsToList arms) e with
    | some ei => return ei
    | none => evalError s!"Incomplete pattern match:\n  expr: {e.pretty}"
  | .unpack a x e1 e2 =>
    let e1' ← evalWHNF e1
    match e1'.unclose with
    | .pack _ eInner _ _ _ =>
      match ← pmatch [⟨1, .var x, e2⟩] eInner with
      | some ei => return ei
      | none => evalError s!"Failed pattern match for unpack on {e1'.pretty}"
    | _ => evalWHNF (.unpack a x e1' e2)
  | .hole => evalError "Trying to evaluate a hole, which should not have passed the type checker."
  | .tryCatch _ _ _ _ => evalError "TryCatch is not supported by the CBN extension yet."
  | v => return v

partial def whnfAppTy (e : Term 0) : EvalM (Term 0) := do
  let v ← evalWHNF e
  match v.unclose with
  | .tyAbs (.inl _) inner => evalWHNF inner
  | _ => evalError s!"Bug: LHS of a type application is not a type abstraction: {v.pretty}"

/-- Deep call-by-name evaluation (`evalInCBNdeep`). -/
partial def evalCBNdeep (t : Term 0) : EvalM (Term 0) := do
  match t with
  | .closed v => evalCBNdeep v
  | .app e1 e2 =>
    let v1 ← evalCBNdeep e1
    match v1.unclose with
    | .prim g args =>
      let v2 ← evalCBNdeep e2
      applyPrimArg g args.toList v2
    | .lam p body =>
      match ← pmatchCBN [⟨_, p, body⟩] e2 with
      | some e3 => evalCBNdeep e3
      | none => evalError s!"Runtime exception: Failed pattern match {p.pretty} in application"
    | .constr c vs =>
      let v2 ← evalCBNdeep e2
      return .constr c (.ofList (vs.toList ++ [v2]))
    | v => evalError s!"CBNdeep: LHS of an application is not a function value {v.pretty}"
  | .global x => lookupGlobal x
  | v =>
    if isValue v then return v
    else
      let v' ← evalWHNF v
      evalCBNdeep v'

/-- `evalIn`: dispatch on the evaluation strategy. -/
partial def evalIn (t : Term 0) : EvalM (Term 0) := do
  if (← read).cbn then
    let v ← evalCBNdeep t
    evalCBV v
  else evalCBV t

end

end Eval

end Granule

end
