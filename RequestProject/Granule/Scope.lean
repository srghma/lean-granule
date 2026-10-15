module

public import RequestProject.Granule.Core

/-!
# Scope resolution and desugaring

Converts the named surface syntax (`SExpr`, `SPat`) into the well-scoped core
syntax (`Term n`, `Pat k`).  Variables bound by enclosing binders become
`Term.var i` with `i : Fin n`; all other variables refer to top-level
definitions or builtins and become `Term.global`.

Also ports `Language.Granule.Interpreter.Desugar.desugar`, which folds the
equations of a definition into a single case expression under lambdas.
-/

@[expose] public section

namespace Granule

mutual

/-- Convert a pattern, returning the number of variables it binds and their
names (left to right). -/
def SPat.toPat : SPat → (k : Nat) × Pat k × Vector String k
  | .var x => ⟨1, .var x, #v[x]⟩
  | .wild => ⟨0, .wild, #v[]⟩
  | .box p =>
    let ⟨k, q, ns⟩ := p.toPat
    ⟨k, .box q, ns⟩
  | .int n => ⟨0, .int n, #v[]⟩
  | .float f => ⟨0, .float f, #v[]⟩
  | .char c => ⟨0, .char c, #v[]⟩
  | .constr c _ ps =>
    let ⟨k, qs, ns⟩ := SPat.toPats ps
    ⟨k, .constr c qs, ns⟩

def SPat.toPats : List SPat → (k : Nat) × Pats k × Vector String k
  | [] => ⟨0, .nil, #v[]⟩
  | p :: ps =>
    let ⟨a, q, na⟩ := p.toPat
    let ⟨b, qs, nb⟩ := SPat.toPats ps
    ⟨a + b, .cons q qs, na ++ nb⟩

end

/-- Find the innermost binding of a name in a scope. -/
def findVar {n : Nat} (ctx : Vector String n) (x : String) : Option (Fin n) :=
  (List.finRange n).reverse.find? fun i => ctx[i] == x

/-- Scope resolution of expressions. -/
partial def SExpr.toTerm {n : Nat} (ctx : Vector String n) : SExpr → Term n
  | .app f a => .app (f.toTerm ctx) (a.toTerm ctx)
  | .appTy f t => .appTy (f.toTerm ctx) t
  | .binop o a b => .binop o (a.toTerm ctx) (b.toTerm ctx)
  | .letDiamond p _ e1 e2 =>
    let ⟨_, q, ns⟩ := p.toPat
    .letDiamond q (e1.toTerm ctx) (e2.toTerm (ctx ++ ns))
  | .tryCatch e1 p _ e2 e3 =>
    let ⟨_, q, ns⟩ := p.toPat
    .tryCatch (e1.toTerm ctx) q (e2.toTerm (ctx ++ ns)) (e3.toTerm ctx)
  | .case e arms =>
    .case (e.toTerm ctx) (arms.foldr (fun (p, b) acc =>
      let ⟨_, q, ns⟩ := p.toPat
      .cons q (b.toTerm (ctx ++ ns)) acc) .nil)
  | .unpack a x e1 e2 => .unpack a x (e1.toTerm ctx) (e2.toTerm (ctx.push x))
  | .hole _ => .hole
  | .abs p _ b =>
    let ⟨_, q, ns⟩ := p.toPat
    .lam q (b.toTerm (ctx ++ ns))
  | .promote e => .promote (e.toTerm ctx)
  | .pure e => .pure (e.toTerm ctx)
  | .nec e => .nec (e.toTerm ctx)
  | .ref e => .ref (e.toTerm ctx)
  | .constr c => .constr c .nil
  | .var x =>
    match findVar ctx x with
    | some i => .var i
    | none => .global x
  | .int i => .int i
  | .float f => .float f
  | .char c => .char c
  | .string s => .string s
  | .pack t e x k t' => .pack t (e.toTerm ctx) x k t'
  | .tyAbs b e => .tyAbs b (e.toTerm ctx)

/-- Convert a closed surface expression. -/
def SExpr.toClosed (e : SExpr) : Term 0 := e.toTerm #v[]

/-- Pair construction as used by the desugarer (Haskell's `pair`). -/
def desugarPair (e1 e2 : SExpr) : SExpr := .app (.app (.constr "(,)") e1) e2

/-- `desugar` from `Language.Granule.Interpreter.Desugar`: fold the equations
`f p1 .. pn = e` of a definition into
`\v1 -> .. \vn -> case (((), v1), .., vn) of ((_, p1), .., pn) -> e; ..`. -/
def desugarDef (d : Def) : SExpr :=
  let numArgs := match d.equations with
    | e :: _ => e.pats.length
    | [] => 0
  let vars := (List.range numArgs).map fun i => s!" internal{i + 1}"
  let guard := vars.foldl (fun acc v => desugarPair acc (.var v)) (.constr "()")
  let cases := d.equations.map fun eq =>
    (eq.pats.foldl (fun acc p => SPat.constr "(,)" [] [acc, p]) .wild, eq.body)
  let tys := d.scheme.ty.params
  vars.zipIdx.foldr (fun (v, i) body => .abs (.var v) tys[i]? body) (.case guard cases)

/-- The closed core term of a definition. -/
def Def.toTerm (d : Def) : Term 0 := (desugarDef d).toClosed

end Granule

end
