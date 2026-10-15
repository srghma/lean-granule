module

public import RequestProject.Granule.Syntax
public import RequestProject.Granule.Lexer

/-!
# Granule parser

A recursive-descent port of the Happy grammar `Language.Granule.Syntax.Parser`.
Operator precedences follow the `%left`/`%right` declarations of the Happy
file, including Happy's default of *shifting* whenever an operator has no
declared precedence (so for example `a + b == c` parses as `a + (b == c)`,
exactly as in the Haskell implementation).
-/

@[expose] public section

namespace Granule

namespace Parser

/-- Parser monad: tokens are read-only, the state is the current position,
and failures record the position of the furthest error. -/
abbrev P := ReaderT (Array Token) (StateT Nat (Except Nat))

instance {α : Type} : Inhabited (P α) := ⟨fun _ _ => .error 0⟩

def eofTok : Token := ⟨.op "<eof>", 0, 0⟩

def peekAt (k : Nat) : P Tok := do
  let ts ← read
  let i ← get
  return (ts.getD (i + k) eofTok).tok

def peek : P Tok := peekAt 0

def bump : P Unit := modify (· + 1)

def failHere {α : Type} : P α := do throw (← get)

def next : P Tok := do let t ← peek; bump; return t

/-- Backtracking choice, reporting the furthest failure. -/
def alt {α : Type} (p q : P α) : P α :=
  tryCatch p fun e1 => tryCatch q fun e2 => throw (max e1 e2)

instance {α : Type} : OrElse (P α) := ⟨fun p q => alt p (q ())⟩

def optionalP {α : Type} (p : P α) : P (Option α) := alt (some <$> p) (pure none)

def isOp (s : String) : P Bool := return (← peek) == .op s
def isKw (s : String) : P Bool := return (← peek) == .kw s

def expectOp (s : String) : P Unit := do if ← isOp s then bump else failHere
def expectKw (s : String) : P Unit := do if ← isKw s then bump else failHere

def expectSym : P String := do
  match ← peek with
  | .sym s => bump; return s
  | _ => failHere

def expectConstr : P String := do
  match ← peek with
  | .constr s => bump; return s
  | _ => failHere

def expectNL : P Unit := do
  match ← peek with
  | .nl =>
    bump
    while (← peek) == .nl do bump
  | _ => failHere

/-- Many (zero or more) with backtracking on the failing attempt. -/
partial def many {α : Type} (p : P α) : P (List α) := do
  match ← optionalP p with
  | some a => return a :: (← many p)
  | none => return []

def many1 {α : Type} (p : P α) : P (List α) := do
  let a ← p
  return a :: (← many p)

/-! ## Generic operator-precedence (Happy/yacc) handling -/

inductive Assoc where | left | right | none

/-- Precedence levels from the order of the `%left`/`%right` declarations. -/
def precOf : String → Option (Nat × Assoc)
  | "∘" => some (1, .right)
  | "->" => some (3, .right)
  | ":" => some (4, .left)
  | "×" => some (5, .right)
  | ".." => some (6, .left)
  | "+" | "-" => some (7, .left)
  | "*" => some (8, .left)
  | "&" => some (9, .left)
  | "^" => some (10, .left)
  | "|" => some (11, .left)
  | "." => some (12, .left)
  | _ => none

/-- Yacc rule: reduce the operator on the stack before shifting `o2`? -/
def shouldReduce (o1 o2 : String) : Bool :=
  match precOf o1, precOf o2 with
  | some (p1, a1), some (p2, _) => p1 > p2 || (p1 == p2 && match a1 with | .left => true | _ => false)
  | _, _ => false

/-- Resolve a sequence `e0 op1 e1 op2 e2 ...` with Happy's conflict resolution. -/
def resolveOps {α β : Type} (opName : β → String) (mk : β → α → α → α)
    (e0 : α) (rest : List (β × α)) : α := Id.run do
  let mut operands : List α := [e0]
  let mut ops : List β := []
  for (o, e) in rest do
    -- reduce while the top of the stack should be reduced before shifting o
    let mut continue_ := true
    while continue_ do
      match ops, operands with
      | o1 :: ops', r :: l :: operands' =>
        if shouldReduce (opName o1) (opName o) then
          ops := ops'
          operands := mk o1 l r :: operands'
        else continue_ := false
      | _, _ => continue_ := false
    ops := o :: ops
    operands := e :: operands
  -- reduce everything left
  let mut result := operands
  for o in ops do
    match result with
    | r :: l :: rs => result := mk o l r :: rs
    | _ => pure ()
  return result.headD e0

/-! ## Types -/

def startsTyAtom : Tok → Bool
  | .constr _ | .sym _ | .int _ | .float _ => true
  | .op "(" | .op "{" => true
  | _ => false

mutual

/-- `TyAtom` (without the left-recursive `TyAtom ':' Kind` which we only allow
inside parentheses). -/
partial def tyAtom : P Ty := do
  match ← peek with
  | .constr "Type" => bump; return .type 0
  | .constr "Semiring" => bump; return .con "Semiring"
  | .constr s => bump; return .con s
  | .sym s => bump; return .var s
  | .int n => bump; return .grade n
  | .float s => bump; return .rational s
  | .op "{" =>
    bump
    let elems ← coeffSet
    expectOp "}"
    let opp ← oppositeMarker
    return .set opp elems
  | .op "(" =>
    bump
    if ← isOp "," then
      bump; expectOp ")"; return .con ","
    else if ← isKw "forall" then
      bump; expectOp "{"; let x ← expectSym; expectOp ":"; let k ← ty; expectOp "}"
      expectOp "."; let t ← ty; expectOp ")"
      return .forall x k t
    else
      let t ← ty
      if ← isOp "," then
        bump; let t2 ← ty; expectOp ")"
        return .app (.app (.con ",") t) t2
      else if ← isOp ":" then
        bump; let k ← ty; expectOp ")"
        return .sig t k
      else
        expectOp ")"; return t
  | _ => failHere

/-- A `.` after a set literal marks the opposite order, unless it starts
`.<=` / `.>=`. -/
partial def oppositeMarker : P Bool := do
  if ← isOp "." then
    let t ← peekAt 1
    if t == .op "<=" || t == .op ">=" then return false
    -- a `.` followed by something that cannot continue is the forall dot; we
    -- only treat it as an opposite marker when not directly followed by a type
    bump; return true
  else return false

partial def coeffSet : P (List Ty) := do
  let elem : P Ty := do
    match ← peek with
    | .constr s => bump; return .con s
    | .sym s => bump; return .var s
    | _ => failHere
  match ← optionalP elem with
  | none => return []
  | some e =>
    let mut es := [e]
    while ← isOp "," do
      bump; es := es ++ [← elem]
    return es

/-- `TyJuxt`; also reports whether it consists of a single atom. -/
partial def tyJuxt : P (Ty × Bool) := do
  let a ← tyAtom
  let t ← peek
  let infixOps := ["+", "-", "*", "^", "/\\", "\\/", "<=", ">=", "==", "/=", "=>"]
  match t with
  | .op o =>
    if infixOps.contains o then
      bump; let b ← tyAtom; return (.infix o a b, false)
    else if o == "." && ((← peekAt 1) == .op "<=" || (← peekAt 1) == .op ">=") then
      bump; let o' ← next
      let b ← tyAtom
      let name := match o' with | .op s => "." ++ s | _ => "."
      return (.infix name a b, false)
    else juxtRest a true
  | _ => juxtRest a true

partial def juxtRest (acc : Ty) (single : Bool) : P (Ty × Bool) := do
  let t ← peek
  if t == .op "`" then
    bump; let f ← tyAtom; expectOp "`"
    juxtRest (.app f acc) false
  else if startsTyAtom t then
    match ← optionalP tyAtom with
    | some a => juxtRest (.app acc a) false
    | none => return (acc, single)
  else return (acc, single)

/-- Operand of the binary type operators (`->`, `×`, `&`). -/
partial def tyOperand : P Ty := do
  match ← peek with
  | .op "!" => bump; let t ← tyAtom; return .box (.con "Many") t
  | .op "*" => bump; let t ← tyAtom; return .borrow (.con "Star") t
  | .op "&" => bump; let p ← permission; let t ← tyAtom; return .borrow p t
  | .kw "case" =>
    bump; let t ← ty; expectKw "of"
    let c1 ← tyCase
    let mut cs := [c1]
    while ← isOp ";" do
      bump; cs := cs ++ [← tyCase]
    return .tycase t cs
  | .kw "exists" =>
    bump; expectOp "{"; let x ← expectSym; expectOp ":"; let k ← ty; expectOp "}"
    expectOp "."; let t ← ty
    return .exists x k t
  | .op "(" =>
    -- dependent function type `(x : A) -> B` / `(x : A) % c -> B`
    let dep : P Ty := do
      bump; let x ← expectSym; expectOp ":"; let a ← ty; expectOp ")"
      if ← isOp "->" then
        bump; let b ← ty; return .fn (some x) none a b
      else
        expectOp "%"; let c ← coeffect; expectOp "->"; let b ← ty
        return .fn (some x) (some c) a b
    dep <|> postfixed
  | _ => postfixed

partial def postfixed : P Ty := do
  let (t, single) ← tyJuxt
  if !single then return t
  match ← peek with
  | .op "[" =>
    bump
    if ← isOp "]" then
      bump
      return .box (.infix ".." (.grade 0) Ty.infinity) t
    let c ← coeffect; expectOp "]"; return .box c t
  | .op "*{" => bump; let g ← expectConstr; expectOp "}"; return .star (.con g) t
  | .op "<" => bump; let e ← effect; expectOp ">"; return .diamond e t
  | _ => return t

partial def tyCase : P (Ty × Ty) := do
  let a ← tyOperand; expectOp "->"; let b ← ty; return (a, b)

partial def effect : P Ty := do
  if ← isOp ">" then return .con "Pure"
  if ← isOp "{" then
    bump
    let e1 ← expectConstr
    let mut es := [Ty.con e1]
    while ← isOp "," do
      bump; es := es ++ [.con (← expectConstr)]
    expectOp "}"
    return .set false es
  let (t, _) ← tyJuxt
  return t

partial def permission : P Ty := do
  let atom : P Ty := do
    match ← peek with
    | .constr s => bump; return .con s
    | .sym s => bump; return .var s
    | .int n =>
      bump
      if ← isOp "/" then
        bump
        match ← next with
        | .int d => return .fraction n d
        | _ => failHere
      else return .fraction n 1
    | .op "(" => bump; let p ← permission; expectOp ")"; return p
    | _ => failHere
  let a ← atom
  let mut rest : List (String × Ty) := []
  while (← isOp "+") || (← isOp "*") do
    let o ← next
    let b ← atom
    rest := rest ++ [(match o with | .op s => s | _ => "+", b)]
  return resolveOps id (fun o l r => .infix o l r) a rest

/-- The binary type operators `->`, `% c ->`, `×`, `&` with Happy precedences. -/
partial def ty : P Ty := do
  let t0 ← tyOperand
  let mut rest : List ((String × Option Ty) × Ty) := []
  let mut go := true
  while go do
    match ← peek with
    | .op "->" => bump; let t ← tyOperand; rest := rest ++ [(("->", none), t)]
    | .op "%" =>
      bump; let c ← coeffect; expectOp "->"; let t ← tyOperand
      rest := rest ++ [(("->", some c), t)]
    | .op "×" => bump; let t ← tyOperand; rest := rest ++ [(("×", none), t)]
    | .op "&" => bump; let t ← tyOperand; rest := rest ++ [(("&", none), t)]
    | _ => go := false
  return resolveOps (·.1) (fun o l r =>
    match o with
    | ("->", g) => .fn none g l r
    | ("×", _) => .app (.app (.con ",") l) r
    | _ => .app (.app (.con "&") l) r) t0 rest

/-- Coeffect (grade) expressions. -/
partial def coeffectAtom : P Ty := do
  match ← peek with
  | .int n => bump; return .grade n
  | .op "." =>
    bump
    match ← next with
    | .int n => return .grade n
    | _ => failHere
  | .op "∞" => bump; return Ty.infinity
  | .float s => bump; return .rational s
  | .constr "Inf" => bump; return Ty.infinity
  | .constr s => bump; return .con s
  | .sym s => bump; return .var s
  | .op "{" =>
    bump; let es ← coeffSet; expectOp "}"
    let opp ← oppositeMarker
    return .set opp es
  | .op "(" =>
    bump
    let c ← coeffect
    if ← isOp "," then
      bump; expectOp ","; let d ← coeffect; expectOp ")"
      return .app (.app (.con ",,") c) d
    else if ← isOp "×" then
      bump; let d ← coeffect; expectOp ")"
      return .app (.app (.con ",,") c) d
    else
      expectOp ")"; return c
  | _ => failHere

partial def coeffect : P Ty := do
  let c0 ← coeffectAtom
  let ops := ["..", "+", "*", "-", "^", "/\\", "\\/"]
  let mut rest : List (String × Ty) := []
  let mut go := true
  while go do
    match ← peek with
    | .op o =>
      if ops.contains o then
        bump; let c ← coeffectAtom; rest := rest ++ [(o, c)]
      else if o == ":" then
        -- `Coeffect ':' Kind` : treat as a postfix operator on the last operand
        bump; let k ← ty
        match rest.getLast? with
        | some (o', c) => rest := rest.dropLast ++ [(o', .sig c k)]
        | none => rest := []; go := false; return .sig c0 k
      else go := false
    | _ => go := false
  return resolveOps id (fun o l r => .infix o l r) c0 rest

end

/-- A constraint in a type scheme. -/
partial def constraint : P Ty := do
  if ← isKw "mut" then
    bump; let t ← tyAtom; return .infix "mut" t t
  let (t, single) ← tyJuxt
  if single then
    match ← peek with
    | .op o =>
      if [">", "<", "⨱"].contains o then
        bump; let b ← tyAtom; return .infix o t b
      else return t
    | _ => return t
  else return t

def constraints : P (List Ty) := do
  let c ← constraint
  let mut cs := [c]
  while ← isOp "," do
    bump; cs := cs ++ [← constraint]
  return cs

def vars1 : P (List String) := many1 expectSym

def varSig : P (List (String × Ty)) := do
  let vs ← vars1
  if ← isOp ":" then
    bump; let k ← ty; return vs.map (·, k)
  else return vs.map fun v => (v, .var ("_k" ++ v))

def forallSig : P (List (String × Ty)) := do
  if ← isOp "{" then
    bump
    let s ← varSig
    let mut sigs := s
    while ← isOp "," do
      bump; sigs := sigs ++ (← varSig)
    expectOp "}"
    return sigs
  else
    let vs ← vars1
    return vs.map fun v => (v, .var ("_k" ++ v))

def typeScheme : P TypeScheme := do
  if ← isKw "forall" then
    bump
    let bs ← forallSig
    expectOp "."
    let cs ← optionalP (do expectOp "{"; let cs ← constraints; expectOp "}"; expectOp "=>"; return cs)
    let t ← ty
    return { binders := bs, constraints := cs.getD [], ty := t }
  else
    let withCs : P TypeScheme := do
      expectOp "{"; let cs ← constraints; expectOp "}"; expectOp "=>"; let t ← ty
      return { constraints := cs, ty := t }
    withCs <|> (do let t ← ty; return { ty := t })

/-! ## Patterns -/

mutual

partial def pAtom : P SPat := do
  match ← peek with
  | .sym x => bump; return .var x
  | .op "_" => bump; return .wild
  | .int n => bump; return .int n
  | .float s => bump; return .float (parseFloatLit s)
  | .char c => bump; return .char c
  | .constr c => bump; return .constr c [] []
  | .op "(" =>
    bump
    let p ← (do let p ← nAryConstr; expectOp ")"; return p) <|>
      (do let a ← pMolecule; expectOp ","; let b ← pMolecule; expectOp ")"
          return SPat.constr "," [] [a, b])
    return p
  | .op "[" =>
    bump
    let p ← nAryConstr <|> pAtom
    expectOp "]"
    return .box p
  | .op "!" => bump; let p ← pAtom; return .box p
  | _ => failHere

partial def pMolecule : P SPat := nAryConstr <|> pAtom

partial def nAryConstr : P SPat := do
  let c ← expectConstr
  let binds ← many (do expectOp "{"; let v ← expectSym; expectOp "}"; return v)
  let ps ← many1 pAtom
  return .constr c binds ps

/-- Float literal parsing (`read` on a `@float` lexeme). -/
partial def parseFloatLit (s : String) : Float :=
  let neg := s.startsWith "-"
  let s' := if neg then s.drop 1 else s.toSlice
  match (s'.toString).splitOn "." with
  | [i, f] =>
    let mant := (i ++ f).toNat!
    let v := Float.ofScientific mant true f.length
    if neg then -v else v
  | _ => 0

end

def mkBinop (o : String) (l r : SExpr) : SExpr :=
  match o with
  | "+" => .binop .plus l r
  | "-" => .binop .minus l r
  | "*" => .binop .times l r
  | "/" => .binop .div l r
  | "<" => .binop .lesser l r
  | ">" => .binop .greater l r
  | "<=" => .binop .lesserEq l r
  | ">=" => .binop .greaterEq l r
  | "==" => .binop .eq l r
  | "/=" => .binop .notEq l r
  | _ => .app (.app (.var "compose") l) r


/-! ## Expressions -/

def startsAtom : Tok → Bool
  | .op "(" | .int _ | .float _ | .sym _ | .op "[" | .op "#" | .constr _ | .char _
  | .string _ | .op "{!" | .op "?" | .kw "share" => true
  | _ => false

mutual

partial def expr : P SExpr := do
  match ← peek with
  | .kw "let" =>
    bump
    letBinds
  | .op "/\\" =>
    bump
    if ← isOp "(" then
      bump
      let one : P (String × Ty) := do
        let v ← expectSym; expectOp ":"; let t ← ty; return (v, t)
      let b1 ← one
      let mut bs := [b1]
      while ← isOp "," do
        bump; bs := bs ++ [← one]
      expectOp ")"; expectOp "->"
      let e ← expr
      return bs.foldl (fun e b => .tyAbs (.inl b) e) e
    else
      expectOp "{"
      let v1 ← expectSym
      let mut vs := [v1]
      while ← isOp "," do
        bump; vs := vs ++ [← expectSym]
      expectOp "}"; expectOp "."
      let e ← expr
      return .tyAbs (.inr vs) e
  | .op "\\" =>
    bump
    let annotated : P SExpr := do
      expectOp "("; let p ← pAtom; expectOp ":"; let t ← ty; expectOp ")"
      expectOp "->"; let e ← expr
      return .abs p (some t) e
    let plain : P SExpr := do
      let p ← pAtom; expectOp "->"; let e ← expr
      return .abs p none e
    annotated <|> plain
  | .kw "try" =>
    bump
    let e1 ← expr
    expectKw "as"; expectOp "["; let p ← pAtom; expectOp "]"
    let t ← optionalP (do expectOp ":"; ty)
    expectKw "in"
    let e2 ← expr
    expectKw "catch"
    let e3 ← expr
    return .tryCatch e1 p t e2 e3
  | .kw "case" =>
    bump
    let e ← expr
    expectKw "of"
    let arms ← cases
    return .case e arms
  | .kw "if" =>
    bump
    let c ← expr; expectKw "then"; let a ← expr; expectKw "else"; let b ← expr
    return .case c [(.constr "True" [] [], a), (.constr "False" [] [], b)]
  | .kw "clone" =>
    bump
    let e1 ← expr; expectKw "as"; let p ← pAtom; let t ← optionalP (do expectOp ":"; ty)
    expectKw "in"; let e2 ← expr
    return .app (.app (.var "uniqueBind") (.abs p t e2)) e1
  | .kw "endorse" =>
    bump
    let e1 ← expr; expectKw "as"; let p ← pAtom; let t ← optionalP (do expectOp ":"; ty)
    expectKw "in"; let e2 ← expr
    return .app (.app (.var "trustedBind") (.abs p t e2)) e1
  | .kw "pack" =>
    bump
    expectOp "<"; let t ← ty; expectOp ","; let e ← atom; expectOp ">"
    expectKw "as"; expectKw "exists"; expectOp "{"; let x ← expectSym; expectOp ":"
    let k ← ty; expectOp "}"; expectOp "."; let t' ← ty
    return .pack t e x k t'
  | .kw "unpack" =>
    bump
    expectOp "<"; let a ← expectSym; expectOp ","; let x ← expectSym; expectOp ">"
    expectOp "="; let e1 ← expr; expectKw "in"; let e2 ← expr
    return .unpack a x e1 e2
  | _ => form

/-- After `let`: either a chain of `p = e;` bindings or of `p <- e;` bindings. -/
partial def letBinds : P SExpr := do
  let pat ← nAryConstr <|> pAtom
  let t ← optionalP (do expectOp ":"; ty)
  match ← peek with
  | .op "=" =>
    bump
    let e1 ← expr
    let body ← multiLet false
    return .app (.abs pat t body) e1
  | .op "<-" =>
    bump
    let e1 ← expr
    let body ← multiLet true
    return .letDiamond pat t e1 body
  | _ => failHere

partial def multiLet (eff : Bool) : P SExpr := do
  match ← peek with
  | .op ";" =>
    bump
    let pat ← if eff then pAtom else (nAryConstr <|> pAtom)
    let t ← optionalP (do expectOp ":"; ty)
    if eff then expectOp "<-" else expectOp "="
    let e1 ← expr
    let body ← multiLet eff
    if eff then return .letDiamond pat t e1 body
    else return .app (.abs pat t body) e1
  | .kw "in" => bump; expr
  | _ => failHere

partial def cases : P (List (SPat × SExpr)) := do
  let c ← caseArm
  let rest ← optionalP (do expectOp ";"; cases)
  return c :: rest.getD []

partial def caseArm : P (SPat × SExpr) := do
  let p ← nAryConstr <|> pAtom
  expectOp "->"
  let e ← expr
  return (p, e)

/-- Binary operator layer (`Form`). -/
partial def form : P SExpr := do
  let e0 ← juxt
  let opsList := ["+", "-", "*", "/", "<", ">", "<=", ">=", "==", "/=", "∘", "."]
  let mut rest : List (String × SExpr) := []
  let mut go := true
  while go do
    match ← peek with
    | .op o =>
      if opsList.contains o then
        bump; let e ← juxt; rest := rest ++ [(o, e)]
      else go := false
    | _ => go := false
  return resolveOps id mkBinop e0 rest

partial def juxt : P SExpr := do
  let a ← atom
  juxtLoop a

partial def juxtLoop (acc : SExpr) : P SExpr := do
  let t ← peek
  if t == .op "`" then
    bump; let f ← atom; expectOp "`"
    juxtLoop (.app f acc)
  else if t == .op "@" then
    bump; let ty ← tyAtom
    juxtLoop (.appTy acc ty)
  else if t == .op ":" then
    bump; let ty ← tyAtom
    juxtLoop (.app (.abs (.var "x") (some ty) (.var "x")) acc)
  else if startsAtom t then
    let a ← atom
    juxtLoop (.app acc a)
  else return acc

partial def atom : P SExpr := do
  match ← peek with
  | .op "(" =>
    bump
    let e ← expr
    if ← isOp "," then
      bump; let e2 ← expr; expectOp ")"
      return SExpr.pair e e2
    else
      expectOp ")"; return e
  | .int n => bump; return .int n
  | .float s => bump; return .float (parseFloatLit s)
  | .sym x => bump; return .var x
  | .op "[" => bump; let e ← expr; expectOp "]"; return .promote e
  | .op "#" =>
    bump
    match ← next with
    | .int n => return .nec (.int n)
    | .float s => return .nec (.float (parseFloatLit s))
    | .constr c => return .nec (.constr c)
    | .char c => return .nec (.char c)
    | .string s => return .nec (.string s)
    | _ => failHere
  | .constr c => bump; return .constr c
  | .char c => bump; return .char c
  | .string s => bump; return .string s
  | .op "?" => bump; return .hole []
  | .op "{!" =>
    bump
    let mut vs : List String := []
    while !(← isOp "!}") do
      match ← next with
      | .sym x => vs := vs ++ [x]
      | .op "<eof>" => failHere
      | _ => pure ()
    bump
    return .hole vs
  | .kw "share" => bump; let e ← expr; return .app (.var "uniqueReturn") e
  | _ => failHere

end

/-! ## Top level -/

def binding : P (String × Equation) := do
  let name ← expectSym
  let ps ← many pAtom
  expectOp "="
  let e ← expr
  return (name, { pats := ps, body := e })

partial def bindings : P (String × List Equation) := do
  let (n, eq) ← binding
  let rest ← optionalP (do expectOp ";"; expectNL; bindings)
  match rest with
  | none => return (n, [eq])
  | some (n', eqs) =>
    if n == n' then return (n, eq :: eqs) else failHere

/-- Specs (`spec ...`) are only used by the synthesiser: skip to the end of line. -/
def skipSpec : P Unit := do
  expectKw "spec"
  while (← peek) != .nl && (← peek) != .op "<eof>" do bump

def definition : P Def := do
  let name ← expectSym
  expectOp ":"
  let sch ← typeScheme
  expectNL
  let _ ← optionalP (do skipSpec; expectNL)
  let (n, eqs) ← bindings
  if n != name then failHere
  return { name := name, equations := eqs, scheme := sch }

def tyVars : P (List (String × Ty)) :=
  many ((do expectOp "("; let v ← expectSym; expectOp ":"; let k ← ty; expectOp ")"; return (v, k))
    <|> (do let v ← expectSym; return (v, Ty.type 0)))

partial def dataConstrs : P (List DataConstr) := do
  let one : P DataConstr :=
    (do let c ← expectConstr; expectOp ":"; let s ← typeScheme; return DataConstr.indexed c s)
    <|> (do let c ← expectConstr; let ps ← many tyAtom; return DataConstr.nonIndexed c ps)
  match ← optionalP one with
  | none => return []
  | some c =>
    if (← isOp "|") || (← isOp ";") then
      bump; return c :: (← dataConstrs)
    else return [c]

def dataDecl : P DataDecl := do
  expectKw "data"
  let name ← expectConstr
  let vs ← tyVars
  let k ← optionalP (do expectOp ":"; ty)
  if (← isKw "where") || (← isOp "=") then bump else failHere
  let cs ← dataConstrs
  return { name := name, tyVars := vs, kind := k, constrs := cs }

def importDecl : P String := do
  match ← peek with
  | .import s =>
    bump
    let path := (s.drop 6).toString.trimAscii.toString
    return String.ofList (path.toList.map fun c => if c == '.' then '/' else c) ++ ".gr"
  | _ => failHere

inductive Item where
  | defn (d : Def)
  | data (d : DataDecl)
  | imp (i : String)

partial def defs : P AST := do
  let item ← (Item.data <$> dataDecl) <|> (Item.imp <$> importDecl) <|> (Item.defn <$> definition)
  let rest ← if (← peek) == .nl then do expectNL; defs else pure {}
  match item with
  | .defn d => return { rest with defs := d :: rest.defs }
  | .data d => return { rest with dataDecls := d :: rest.dataDecls }
  | .imp i => return { rest with imports := i :: rest.imports }

partial def topLevel : P (AST × List Extension) := do
  match ← peek with
  | .kw "module" =>
    bump
    let m ← expectConstr
    if ← isKw "hiding" then
      bump; expectOp "("
      let _ ← expectConstr
      while ← isOp "," do
        bump; let _ ← expectConstr
      expectOp ")"
    expectKw "where"
    expectNL
    let ast ← defs
    return ({ ast with moduleName := some m }, [])
  | .pragma =>
    bump
    let c ← expectConstr
    match Extension.parse c with
    | some e =>
      expectNL
      let (ast, exts) ← topLevel
      return (ast, e :: exts)
    | none => failHere
  | _ => return (← defs, [])

/-- Run a parser on a full token list (must consume everything). -/
def runP {α : Type} (p : P α) (toks : List Token) : Except Nat α :=
  let arr := toks.toArray
  match (do let a ← p; if (← peek) == .op "<eof>" then pure a else failHere : P α).run arr |>.run 0 with
  | .ok (a, _) => .ok a
  | .error e => .error e

end Parser

/-- Parse a Granule source file into an AST and its language extensions. -/
def parseDefs (file : String) (input : String) : Except String (AST × List Extension) := do
  let toks ← scanTokens input
  match Parser.runP Parser.topLevel toks with
  | .ok r => .ok r
  | .error i =>
    match toks[i]? with
    | some t => .error s!"{file}:{t.line}:{t.col}: parse error"
    | none => .error "Premature end of file"

/-- Parse a single expression (used in tests). -/
def parseExpr (input : String) : Except String SExpr := do
  let toks ← scanTokens input
  match Parser.runP Parser.expr toks with
  | .ok r => .ok r
  | .error i => .error s!"parse error at token {i}"

end Granule

end
