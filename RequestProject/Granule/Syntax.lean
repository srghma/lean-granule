module

/-!
# Granule surface syntax

A port of `Language.Granule.Syntax.{Type,Pattern,Expr,Def}` from the Haskell
implementation.  This is the *named* syntax produced by the parser.  It is
converted into the well-scoped core syntax `Granule.Term n`
(see `Granule/Core.lean`) by `Granule/Scope.lean`.

Spans and annotations from the Haskell AST are dropped: they are only used for
error reporting by the type checker.
-/

@[expose] public section

namespace Granule

/-- Binary operators (`Language.Granule.Syntax.Expr.Operator`). -/
inductive Operator where
  | lesser | lesserEq | greater | greaterEq | eq | notEq | plus | times | div | minus
  deriving Repr, BEq, Inhabited, DecidableEq

def Operator.pretty : Operator → String
  | .lesser => "<" | .lesserEq => "≤" | .greater => ">" | .greaterEq => "≥"
  | .eq => "≡" | .notEq => "≠" | .plus => "+" | .times => "*" | .div => "/" | .minus => "-"

/-- Types, kinds and grades (`Language.Granule.Syntax.Type.Type`). -/
inductive Ty where
  | type (level : Nat)
  | con (name : String)
  | var (name : String)
  | app (f a : Ty)
  /-- `FunTy (optional dependent name) (optional grade) argument result` -/
  | fn (name : Option String) (grade : Option Ty) (a b : Ty)
  | box (grade t : Ty)
  | diamond (eff t : Ty)
  | star (guarantee t : Ty)
  | borrow (perm t : Ty)
  | grade (n : Int)
  | rational (s : String)
  | fraction (n d : Int)
  | infix (op : String) (a b : Ty)
  /-- `TySet polarity elements`; `opposite = true` is the opposite order. -/
  | set (opposite : Bool) (elems : List Ty)
  | sig (t k : Ty)
  | tycase (t : Ty) (cases : List (Ty × Ty))
  | exists (x : String) (k t : Ty)
  | forall (x : String) (k t : Ty)
  deriving Repr, Inhabited, BEq

namespace Ty

def infinity : Ty := .con "Infinity"

/-- Left-most type in a chain of applications. -/
def leftmost : Ty → Ty
  | .app f _ => leftmost f
  | t => t

/-- Arity of a function type (number of arrows at the top level). -/
def arity : Ty → Nat
  | .fn _ _ _ b => arity b + 1
  | _ => 0

/-- Parameter types of a function type. -/
def params : Ty → List Ty
  | .fn _ _ a b => a :: params b
  | _ => []

/-- Result type of a function type. -/
def result : Ty → Ty
  | .fn _ _ _ b => result b
  | t => t

/-- Arguments of a type application. -/
def appArgs : Ty → List Ty
  | .app f a => appArgs f ++ [a]
  | _ => []

/-- Identifier printing as in `Pretty Id`: drop `.` and backticks. -/
def prettyId (s : String) : String :=
  String.ofList (s.toList.filter fun c => c != '.' && c != '`')

/-- Whether a type is printed without parentheses when nested. -/
def isAtomic : Ty → Bool
  | .con _ | .var _ | .grade _ | .rational _ | .fraction _ _ | .set _ _ | .sig _ _ => true
  | .app (.app (.con ",") _) _ => true
  | _ => false

/-- Pretty printer for types (a port of `Pretty Type`, used for the names of
derived operations and for printing type annotations). -/
partial def pretty : Ty → String
  | .con "Infinity" => "∞"
  | .con s => prettyId s
  | .var v => prettyId v
  | .grade n => toString n
  | .rational s => s
  | .fraction n d => if d == 1 then toString n else s!"{n}/{d}"
  | .type 0 => "Type"
  | .type l => s!"Type {l}"
  | .fn none none a b => s!"{nested a} -> {pretty b}"
  | .fn none (some c) a b => s!"{nested a} % {pretty c} -> {pretty b}"
  | .fn (some x) none a b => s!"({prettyId x} : {pretty a}) -> {pretty b}"
  | .fn (some x) (some c) a b => s!"({prettyId x} : {pretty a}) % {pretty c} -> {pretty b}"
  | .box (.con "Many") t => s!"!{nested t}"
  | .box c t => s!"{nested t} [{pretty c}]"
  | .diamond e t => s!"{nested t} <{pretty e}>"
  | .star (.con "Unique") t => s!"*{nested t}"
  | .star g t => s!"{nested t} *{pretty g}"
  | .borrow (.con "Star") t => s!"*{nested t}"
  | .borrow p t => s!"& {nested p} {nested t}"
  | .app (.app (.con ",") a) b => s!"({pretty a}, {pretty b})"
  | .app (.app (.con ",,") a) b => s!"({pretty a} × {pretty b})"
  | .app (.app (.con "&") a) b => s!"{pretty a} & {pretty b}"
  | .app f a => s!"{pretty f} {nested a}"
  | .infix ".." a b => s!"{nested a}..{nested b}"
  | .infix op a b => s!"{nested a} {op} {nested b}"
  | .set opp ts => "{" ++ ", ".intercalate (ts.map pretty) ++ "}" ++ (if opp then "." else "")
  | .sig t k => s!"({pretty t} : {pretty k})"
  | .tycase t ps =>
      "(case " ++ pretty t ++ " of " ++
        "; ".intercalate (ps.map fun (p, q) => pretty p ++ " : " ++ pretty q) ++ ")"
  | .exists x k t => "exists {" ++ prettyId x ++ " : " ++ pretty k ++ "} . " ++ pretty t
  | .forall x k t => "(forall {" ++ prettyId x ++ " : " ++ pretty k ++ "} . " ++ pretty t ++ ")"
where
  nested (t : Ty) : String := if isAtomic t then pretty t else "(" ++ pretty t ++ ")"

end Ty

/-- Type schemes `forall {binders} . {constraints} => type`. -/
structure TypeScheme where
  binders : List (String × Ty) := []
  constraints : List Ty := []
  ty : Ty
  deriving Repr, Inhabited

/-- Patterns (`Language.Granule.Syntax.Pattern.Pattern`). -/
inductive SPat where
  | var (x : String)
  | wild
  | box (p : SPat)
  | int (n : Int)
  | float (f : Float)
  | char (c : Char)
  /-- Constructor pattern; the list of strings are the requested type-variable
  bindings `C {a} p1 .. pn` (only relevant to the type checker). -/
  | constr (c : String) (tyBinds : List String) (ps : List SPat)
  deriving Repr, Inhabited

namespace SPat

/-- Variables bound by a pattern, left to right. -/
partial def boundVars : SPat → List String
  | .var x => [x]
  | .box p => boundVars p
  | .constr _ _ ps => ps.flatMap boundVars
  | _ => []

end SPat

/-- Binder of a type abstraction `/\(x : k) -> e` (left) or `/\{a, b}. e` (right). -/
abbrev TyAbsBinder := Sum (String × Ty) (List String)

/-- Expressions and values of the surface language
(`Language.Granule.Syntax.Expr.{Expr,Value}` merged into one type). -/
inductive SExpr where
  -- computations (`ExprF`)
  | app (f a : SExpr)
  | appTy (f : SExpr) (t : Ty)
  | binop (op : Operator) (a b : SExpr)
  | letDiamond (p : SPat) (t : Option Ty) (e1 e2 : SExpr)
  | tryCatch (e1 : SExpr) (p : SPat) (t : Option Ty) (e2 e3 : SExpr)
  | case (e : SExpr) (arms : List (SPat × SExpr))
  | unpack (tyVar var : String) (e1 e2 : SExpr)
  | hole (vars : List String)
  -- values (`ValueF`)
  | abs (p : SPat) (t : Option Ty) (body : SExpr)
  | promote (e : SExpr)
  | pure (e : SExpr)
  | nec (e : SExpr)
  | ref (e : SExpr)
  | constr (c : String)
  | var (x : String)
  | int (n : Int)
  | float (f : Float)
  | char (c : Char)
  | string (s : String)
  | pack (ty : Ty) (e : SExpr) (x : String) (k ty' : Ty)
  | tyAbs (binder : TyAbsBinder) (e : SExpr)
  deriving Repr, Inhabited

namespace SExpr

/-- Haskell's list difference `xs \\ ys`: removes the first occurrence of each
element of `ys` from `xs`. -/
def listDiff (xs ys : List String) : List String := ys.foldl (fun acc y => acc.erase y) xs

/-- Free (term) variables, a port of `freeVars` from the `Term` instances of
`Value` and `Expr`. -/
partial def freeVars : SExpr → List String
  | .abs p _ e => listDiff (freeVars e) p.boundVars
  | .var x => [x]
  | .pure e | .promote e | .nec e | .ref e => freeVars e
  | .int _ | .float _ | .constr _ | .char _ | .string _ => []
  | .pack _ e _ _ _ => freeVars e
  | .tyAbs _ e => freeVars e
  | .app a b | .binop _ a b => freeVars a ++ freeVars b
  | .appTy a _ => freeVars a
  | .letDiamond p _ e1 e2 => freeVars e1 ++ listDiff (freeVars e2) p.boundVars
  | .tryCatch e1 p _ e2 e3 =>
      freeVars e1 ++ listDiff (freeVars e2) p.boundVars ++ freeVars e3
  | .case e arms => freeVars e ++ arms.flatMap fun (p, b) => listDiff (freeVars b) p.boundVars
  | .unpack _ x e1 e2 => freeVars e1 ++ listDiff (freeVars e2) [x]
  | .hole _ => []

/-- Pair construction `(e1, e2)`. -/
def pair (e1 e2 : SExpr) : SExpr := .app (.app (.constr ",") e1) e2

end SExpr

/-- An equation `f p1 .. pn = e` of a definition. -/
structure Equation where
  pats : List SPat
  body : SExpr
  deriving Repr, Inhabited

/-- A top-level definition with its type signature. -/
structure Def where
  name : String
  equations : List Equation
  scheme : TypeScheme
  deriving Repr, Inhabited

/-- Data constructors: either GADT-style `C : forall .. . t` or `C t1 .. tn`. -/
inductive DataConstr where
  | indexed (name : String) (scheme : TypeScheme)
  | nonIndexed (name : String) (params : List Ty)
  deriving Repr, Inhabited

def DataConstr.name : DataConstr → String
  | .indexed n _ => n
  | .nonIndexed n _ => n

structure DataDecl where
  name : String
  tyVars : List (String × Ty)
  kind : Option Ty
  constrs : List DataConstr
  deriving Repr, Inhabited

/-- Language extensions (`Language.Granule.Utils.Extension`). -/
inductive Extension where
  | base | cbn | noTopLevelApprox | securityLevels | report | gradedBase | unsafePromotion
  deriving Repr, BEq, Inhabited, DecidableEq

def Extension.parse : String → Option Extension
  | "Base" => some .base
  | "CBN" => some .cbn
  | "NoTopLevelApprox" => some .noTopLevelApprox
  | "SecurityLevels" => some .securityLevels
  | "Report" => some .report
  | "GradedBase" => some .gradedBase
  | "UnsafePromotion" => some .unsafePromotion
  | _ => none

/-- A parsed module. -/
structure AST where
  dataDecls : List DataDecl := []
  defs : List Def := []
  imports : List String := []
  moduleName : Option String := none
  deriving Repr, Inhabited

end Granule

end
