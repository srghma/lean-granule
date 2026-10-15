module

public import RequestProject.Granule.Syntax

/-!
# Well-scoped core syntax of Granule

`Term n` is the type of Granule expressions whose free variables are drawn from
`Fin n`.  In particular `Term 0` is the type of *closed* terms, which is what
the interpreter evaluates and what values are.

Variables are de Bruijn *levels*: a binder that introduces `k` variables
(a pattern) turns a context of size `n` into one of size `n + k`, where the
outer variables are `Fin.castAdd k i` and the new ones are `Fin.natAdd n j`.

Patterns are indexed by the number of variables they bind: `Pat k` binds `k`
variables, numbered from left to right.

Besides the constructors coming from Granule's `Expr`/`Value` syntax, there are
a few runtime-only constructors used by the interpreter (the Haskell
interpreter uses an extension type `Runtime` for these):
* `closed v` embeds a closed term into any context (this makes substitution
  of closed values constant time, like the Haskell substitution);
* `global x` refers to a top-level definition, data constructor-free builtin
  or primitive;
* `prim f args`: a partially applied primitive (builtin) function;
* `rt i`: a runtime resource (file handle, channel, mutable array, reference);
* `effect f args`: a suspended side-effecting computation (`PureWrapper`);
* `freeImpure`, `freeBind`: the free monad representation used for effect
  handlers.
-/

@[expose] public section

namespace Granule

mutual

/-- Patterns binding `k` variables. -/
inductive Pat : Nat → Type where
  /-- A variable pattern (the string is the source name, kept for printing). -/
  | var : String → Pat 1
  | wild : Pat 0
  | box {k : Nat} : Pat k → Pat k
  | int : Int → Pat 0
  | float : Float → Pat 0
  | char : Char → Pat 0
  | constr {k : Nat} : String → Pats k → Pat k

/-- Lists of patterns; the variables of the first pattern come first. -/
inductive Pats : Nat → Type where
  | nil : Pats 0
  | cons {a b : Nat} : Pat a → Pats b → Pats (a + b)

end

mutual

/-- Granule terms with free variables in `Fin n`. -/
inductive Term : Nat → Type where
  | var {n : Nat} : Fin n → Term n
  | closed {n : Nat} : Term 0 → Term n
  | global {n : Nat} : String → Term n
  | app {n : Nat} : Term n → Term n → Term n
  | appTy {n : Nat} : Term n → Ty → Term n
  | binop {n : Nat} : Operator → Term n → Term n → Term n
  /-- `let p <- e1 in e2` -/
  | letDiamond {n k : Nat} : Pat k → Term n → Term (n + k) → Term n
  /-- `try e1 as [p] in e2 catch e3` -/
  | tryCatch {n k : Nat} : Term n → Pat k → Term (n + k) → Term n → Term n
  | case {n : Nat} : Term n → Arms n → Term n
  /-- `unpack <a, x> = e1 in e2` (the type variable is erased) -/
  | unpack {n : Nat} : String → String → Term n → Term (n + 1) → Term n
  | hole {n : Nat} : Term n
  /-- `\p -> e` -/
  | lam {n k : Nat} : Pat k → Term (n + k) → Term n
  | promote {n : Nat} : Term n → Term n
  | pure {n : Nat} : Term n → Term n
  | nec {n : Nat} : Term n → Term n
  | ref {n : Nat} : Term n → Term n
  | constr {n : Nat} : String → Terms n → Term n
  | int {n : Nat} : Int → Term n
  | float {n : Nat} : Float → Term n
  | char {n : Nat} : Char → Term n
  | string {n : Nat} : String → Term n
  /-- `pack <ty, e> as exists {x : k} . ty'` -/
  | pack {n : Nat} : Ty → Term n → String → Ty → Ty → Term n
  | tyAbs {n : Nat} : TyAbsBinder → Term n → Term n
  | prim {n : Nat} : String → Terms n → Term n
  | rt {n : Nat} : Nat → Term n
  | effect {n : Nat} : String → Terms n → Term n
  | freeImpure {n : Nat} : Term n → Term n
  | freeBind {n k : Nat} : Term n → Pat k → Term (n + k) → Term n

inductive Terms : Nat → Type where
  | nil {n : Nat} : Terms n
  | cons {n : Nat} : Term n → Terms n → Terms n

/-- Case alternatives. -/
inductive Arms : Nat → Type where
  | nil {n : Nat} : Arms n
  | cons {n k : Nat} : Pat k → Term (n + k) → Arms n → Arms n

end

instance {n : Nat} : Inhabited (Term n) := ⟨.hole⟩

namespace Terms

def toList {n : Nat} : Terms n → List (Term n)
  | .nil => []
  | .cons t ts => t :: ts.toList

def ofList {n : Nat} : List (Term n) → Terms n
  | [] => .nil
  | t :: ts => .cons t (ofList ts)

@[simp] theorem toList_ofList {n : Nat} (ts : List (Term n)) : (ofList ts).toList = ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [ofList, toList, ih]

end Terms

/-! ## Renaming and substitution -/

/-- Lift a renaming under a binder of `k` variables. -/
def liftRen {m n : Nat} (ρ : Fin m → Fin n) (k : Nat) : Fin (m + k) → Fin (n + k) :=
  Fin.addCases (fun i => Fin.castAdd k (ρ i)) (fun j => Fin.natAdd n j)

mutual

/-- Apply a renaming of variables. -/
def Term.rename {m n : Nat} (ρ : Fin m → Fin n) : Term m → Term n
  | .var i => .var (ρ i)
  | .closed v => .closed v
  | .global x => .global x
  | .app f a => .app (f.rename ρ) (a.rename ρ)
  | .appTy f t => .appTy (f.rename ρ) t
  | .binop o a b => .binop o (a.rename ρ) (b.rename ρ)
  | .letDiamond (k := k) p e1 e2 => .letDiamond p (e1.rename ρ) (e2.rename (liftRen ρ k))
  | .tryCatch (k := k) e1 p e2 e3 =>
      .tryCatch (e1.rename ρ) p (e2.rename (liftRen ρ k)) (e3.rename ρ)
  | .case e arms => .case (e.rename ρ) (arms.rename ρ)
  | .unpack a x e1 e2 => .unpack a x (e1.rename ρ) (e2.rename (liftRen ρ 1))
  | .hole => .hole
  | .lam (k := k) p b => .lam p (b.rename (liftRen ρ k))
  | .promote e => .promote (e.rename ρ)
  | .pure e => .pure (e.rename ρ)
  | .nec e => .nec (e.rename ρ)
  | .ref e => .ref (e.rename ρ)
  | .constr c ts => .constr c (ts.rename ρ)
  | .int i => .int i
  | .float f => .float f
  | .char c => .char c
  | .string s => .string s
  | .pack t e x k t' => .pack t (e.rename ρ) x k t'
  | .tyAbs b e => .tyAbs b (e.rename ρ)
  | .prim f ts => .prim f (ts.rename ρ)
  | .rt i => .rt i
  | .effect f ts => .effect f (ts.rename ρ)
  | .freeImpure e => .freeImpure (e.rename ρ)
  | .freeBind (k := k) v p e => .freeBind (v.rename ρ) p (e.rename (liftRen ρ k))

def Terms.rename {m n : Nat} (ρ : Fin m → Fin n) : Terms m → Terms n
  | .nil => .nil
  | .cons t ts => .cons (t.rename ρ) (ts.rename ρ)

def Arms.rename {m n : Nat} (ρ : Fin m → Fin n) : Arms m → Arms n
  | .nil => .nil
  | .cons (k := k) p b rest => .cons p (b.rename (liftRen ρ k)) (rest.rename ρ)

end

/-- Weakening: view a term in a larger context. -/
def Term.weaken {n : Nat} (k : Nat) (t : Term n) : Term (n + k) := t.rename (Fin.castAdd k)

/-- Lift a substitution under a binder of `k` variables. -/
def liftSub {m n : Nat} (σ : Fin m → Term n) (k : Nat) : Fin (m + k) → Term (n + k) :=
  Fin.addCases (fun i => (σ i).weaken k) (fun j => .var (Fin.natAdd n j))

mutual

/-- Apply a (parallel) substitution. -/
def Term.subst {m n : Nat} (σ : Fin m → Term n) : Term m → Term n
  | .var i => σ i
  | .closed v => .closed v
  | .global x => .global x
  | .app f a => .app (f.subst σ) (a.subst σ)
  | .appTy f t => .appTy (f.subst σ) t
  | .binop o a b => .binop o (a.subst σ) (b.subst σ)
  | .letDiamond (k := k) p e1 e2 => .letDiamond p (e1.subst σ) (e2.subst (liftSub σ k))
  | .tryCatch (k := k) e1 p e2 e3 =>
      .tryCatch (e1.subst σ) p (e2.subst (liftSub σ k)) (e3.subst σ)
  | .case e arms => .case (e.subst σ) (arms.subst σ)
  | .unpack a x e1 e2 => .unpack a x (e1.subst σ) (e2.subst (liftSub σ 1))
  | .hole => .hole
  | .lam (k := k) p b => .lam p (b.subst (liftSub σ k))
  | .promote e => .promote (e.subst σ)
  | .pure e => .pure (e.subst σ)
  | .nec e => .nec (e.subst σ)
  | .ref e => .ref (e.subst σ)
  | .constr c ts => .constr c (ts.subst σ)
  | .int i => .int i
  | .float f => .float f
  | .char c => .char c
  | .string s => .string s
  | .pack t e x k t' => .pack t (e.subst σ) x k t'
  | .tyAbs b e => .tyAbs b (e.subst σ)
  | .prim f ts => .prim f (ts.subst σ)
  | .rt i => .rt i
  | .effect f ts => .effect f (ts.subst σ)
  | .freeImpure e => .freeImpure (e.subst σ)
  | .freeBind (k := k) v p e => .freeBind (v.subst σ) p (e.subst (liftSub σ k))

def Terms.subst {m n : Nat} (σ : Fin m → Term n) : Terms m → Terms n
  | .nil => .nil
  | .cons t ts => .cons (t.subst σ) (ts.subst σ)

def Arms.subst {m n : Nat} (σ : Fin m → Term n) : Arms m → Arms n
  | .nil => .nil
  | .cons (k := k) p b rest => .cons p (b.subst (liftSub σ k)) (rest.subst σ)

end

/-- Instantiate the `k` variables bound by a pattern at top level with closed
values, producing a closed term. -/
def Term.instantiate {k : Nat} (body : Term (0 + k)) (vals : Fin k → Term 0) : Term 0 :=
  body.subst (Fin.addCases (fun i => Fin.elim0 i) (fun j => (vals j).weaken 0))

/-- Embed a closed term in any context. Values are closed, so substituting
them never needs to traverse them. -/
def Term.ofClosed {n : Nat} : Term 0 → Term n
  | .closed v => .closed v
  | v => .closed v

/-- Remove `closed` wrappers at the root of a closed term. -/
def Term.unclose : Term 0 → Term 0
  | .closed v => v.unclose
  | v => v

/-- A reserved name used to detect occurrences of variables. -/
def markerName : String := "\x00marker"

mutual

/-- Does the term mention the global `markerName`? -/
def Term.hasMarker {m : Nat} : Term m → Bool
  | .global x => x == markerName
  | .hole | .var _ | .closed _ | .int _ | .float _ | .char _ | .string _ | .rt _ => false
  | .app f a | .binop _ f a => f.hasMarker || a.hasMarker
  | .appTy f _ | .promote f | .pure f | .nec f | .ref f | .pack _ f _ _ _ | .tyAbs _ f
  | .freeImpure f => f.hasMarker
  | .letDiamond _ e1 e2 | .unpack _ _ e1 e2 | .freeBind e1 _ e2 => e1.hasMarker || e2.hasMarker
  | .tryCatch e1 _ e2 e3 => e1.hasMarker || e2.hasMarker || e3.hasMarker
  | .lam _ b => b.hasMarker
  | .case e arms => e.hasMarker || arms.hasMarker
  | .constr _ ts | .prim _ ts | .effect _ ts => ts.hasMarker

def Terms.hasMarker {m : Nat} : Terms m → Bool
  | .nil => false
  | .cons t ts => t.hasMarker || ts.hasMarker

def Arms.hasMarker {m : Nat} : Arms m → Bool
  | .nil => false
  | .cons _ b rest => b.hasMarker || rest.hasMarker

end

/-- Does variable `i` occur in `t`?  (Computed by substituting a marker for it.) -/
def Term.occurs {n : Nat} (i : Fin n) (t : Term n) : Bool :=
  (t.subst (n := n) fun j => if j = i then .global markerName else .var j).hasMarker

/-- The variables occurring free in a term (assuming `t` itself does not use
the reserved marker name). -/
def Term.freeVars {n : Nat} (t : Term n) : List (Fin n) :=
  (List.finRange n).filter fun i => t.occurs i

end Granule

end
