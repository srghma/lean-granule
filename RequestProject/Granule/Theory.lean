module

public import RequestProject.Granule.Core

/-!
# Basic metatheory of the well-scoped syntax

Sanity properties of renaming and substitution on `Term n`.
-/

@[expose] public section

namespace Granule

theorem liftRen_id (m k : Nat) : liftRen (id : Fin m → Fin m) k = id := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simp [liftRen]
  · simp [liftRen]

theorem liftRen_comp {a b c : Nat} (ρ : Fin a → Fin b) (τ : Fin b → Fin c) (k : Nat) :
    liftRen τ k ∘ liftRen ρ k = liftRen (τ ∘ ρ) k := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simp [liftRen]
  · simp [liftRen]

mutual

/-- Renaming by the identity does nothing. -/
theorem Term.rename_id {n : Nat} : (t : Term n) → t.rename id = t
  | .var _ | .closed _ | .global _ | .hole | .int _ | .float _ | .char _ | .string _
  | .rt _ => rfl
  | .app f a => by simp [Term.rename, Term.rename_id f, Term.rename_id a]
  | .appTy f _ => by simp [Term.rename, Term.rename_id f]
  | .binop _ a b => by simp [Term.rename, Term.rename_id a, Term.rename_id b]
  | .letDiamond (k := k) _ e1 e2 => by
    simp [Term.rename, liftRen_id, Term.rename_id e1, Term.rename_id e2]
  | .tryCatch e1 _ e2 e3 => by
    simp [Term.rename, liftRen_id, Term.rename_id e1, Term.rename_id e2, Term.rename_id e3]
  | .case e arms => by simp [Term.rename, Term.rename_id e, Arms.rename_id arms]
  | .unpack _ _ e1 e2 => by simp [Term.rename, liftRen_id, Term.rename_id e1, Term.rename_id e2]
  | .lam _ b => by simp [Term.rename, liftRen_id, Term.rename_id b]
  | .promote e => by simp [Term.rename, Term.rename_id e]
  | .pure e => by simp [Term.rename, Term.rename_id e]
  | .nec e => by simp [Term.rename, Term.rename_id e]
  | .ref e => by simp [Term.rename, Term.rename_id e]
  | .constr _ ts => by simp [Term.rename, Terms.rename_id ts]
  | .pack _ e _ _ _ => by simp [Term.rename, Term.rename_id e]
  | .tyAbs _ e => by simp [Term.rename, Term.rename_id e]
  | .prim _ ts => by simp [Term.rename, Terms.rename_id ts]
  | .effect _ ts => by simp [Term.rename, Terms.rename_id ts]
  | .freeImpure e => by simp [Term.rename, Term.rename_id e]
  | .freeBind v _ e => by simp [Term.rename, liftRen_id, Term.rename_id v, Term.rename_id e]

theorem Terms.rename_id {n : Nat} : (ts : Terms n) → ts.rename id = ts
  | .nil => rfl
  | .cons t ts => by simp [Terms.rename, Term.rename_id t, Terms.rename_id ts]

theorem Arms.rename_id {n : Nat} : (as : Arms n) → as.rename id = as
  | .nil => rfl
  | .cons _ b rest => by simp [Arms.rename, liftRen_id, Term.rename_id b, Arms.rename_id rest]

end


mutual

/-- Renamings compose. -/
theorem Term.rename_rename {a b c : Nat} (ρ : Fin a → Fin b) (τ : Fin b → Fin c) :
    (t : Term a) → (t.rename ρ).rename τ = t.rename (τ ∘ ρ)
  | .var _ | .closed _ | .global _ | .hole | .int _ | .float _ | .char _ | .string _
  | .rt _ => rfl
  | .app f x => by simp [Term.rename, Term.rename_rename ρ τ f, Term.rename_rename ρ τ x]
  | .appTy f _ => by simp [Term.rename, Term.rename_rename ρ τ f]
  | .binop _ x y => by simp [Term.rename, Term.rename_rename ρ τ x, Term.rename_rename ρ τ y]
  | .letDiamond (k := k) _ e1 e2 => by
    simp [Term.rename, Term.rename_rename ρ τ e1, Term.rename_rename _ _ e2, liftRen_comp]
  | .tryCatch (k := k) e1 _ e2 e3 => by
    simp [Term.rename, Term.rename_rename ρ τ e1, Term.rename_rename _ _ e2,
      Term.rename_rename ρ τ e3, liftRen_comp]
  | .case e arms => by simp [Term.rename, Term.rename_rename ρ τ e, Arms.rename_rename ρ τ arms]
  | .unpack _ _ e1 e2 => by
    simp [Term.rename, Term.rename_rename ρ τ e1, Term.rename_rename _ _ e2, liftRen_comp]
  | .lam (k := k) _ bd => by simp [Term.rename, Term.rename_rename _ _ bd, liftRen_comp]
  | .promote e => by simp [Term.rename, Term.rename_rename ρ τ e]
  | .pure e => by simp [Term.rename, Term.rename_rename ρ τ e]
  | .nec e => by simp [Term.rename, Term.rename_rename ρ τ e]
  | .ref e => by simp [Term.rename, Term.rename_rename ρ τ e]
  | .constr _ ts => by simp [Term.rename, Terms.rename_rename ρ τ ts]
  | .pack _ e _ _ _ => by simp [Term.rename, Term.rename_rename ρ τ e]
  | .tyAbs _ e => by simp [Term.rename, Term.rename_rename ρ τ e]
  | .prim _ ts => by simp [Term.rename, Terms.rename_rename ρ τ ts]
  | .effect _ ts => by simp [Term.rename, Terms.rename_rename ρ τ ts]
  | .freeImpure e => by simp [Term.rename, Term.rename_rename ρ τ e]
  | .freeBind (k := k) v _ e => by
    simp [Term.rename, Term.rename_rename ρ τ v, Term.rename_rename _ _ e, liftRen_comp]

theorem Terms.rename_rename {a b c : Nat} (ρ : Fin a → Fin b) (τ : Fin b → Fin c) :
    (ts : Terms a) → (ts.rename ρ).rename τ = ts.rename (τ ∘ ρ)
  | .nil => rfl
  | .cons t ts => by simp [Terms.rename, Term.rename_rename ρ τ t, Terms.rename_rename ρ τ ts]

theorem Arms.rename_rename {a b c : Nat} (ρ : Fin a → Fin b) (τ : Fin b → Fin c) :
    (as : Arms a) → (as.rename ρ).rename τ = as.rename (τ ∘ ρ)
  | .nil => rfl
  | .cons (k := k) _ bd rest => by
    simp [Arms.rename, Term.rename_rename _ _ bd, liftRen_comp, Arms.rename_rename ρ τ rest]

end

theorem liftSub_var (m k : Nat) : liftSub (Term.var : Fin m → Term m) k = Term.var := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simp [liftSub, Term.weaken, Term.rename]
  · simp [liftSub]

mutual

/-- The identity substitution does nothing. -/
theorem Term.subst_var {n : Nat} : (t : Term n) → t.subst Term.var = t
  | .var _ | .closed _ | .global _ | .hole | .int _ | .float _ | .char _ | .string _
  | .rt _ => rfl
  | .app f a => by simp [Term.subst, Term.subst_var f, Term.subst_var a]
  | .appTy f _ => by simp [Term.subst, Term.subst_var f]
  | .binop _ a b => by simp [Term.subst, Term.subst_var a, Term.subst_var b]
  | .letDiamond _ e1 e2 => by simp [Term.subst, liftSub_var, Term.subst_var e1, Term.subst_var e2]
  | .tryCatch e1 _ e2 e3 => by
    simp [Term.subst, liftSub_var, Term.subst_var e1, Term.subst_var e2, Term.subst_var e3]
  | .case e arms => by simp [Term.subst, Term.subst_var e, Arms.subst_var arms]
  | .unpack _ _ e1 e2 => by simp [Term.subst, liftSub_var, Term.subst_var e1, Term.subst_var e2]
  | .lam _ b => by simp [Term.subst, liftSub_var, Term.subst_var b]
  | .promote e => by simp [Term.subst, Term.subst_var e]
  | .pure e => by simp [Term.subst, Term.subst_var e]
  | .nec e => by simp [Term.subst, Term.subst_var e]
  | .ref e => by simp [Term.subst, Term.subst_var e]
  | .constr _ ts => by simp [Term.subst, Terms.subst_var ts]
  | .pack _ e _ _ _ => by simp [Term.subst, Term.subst_var e]
  | .tyAbs _ e => by simp [Term.subst, Term.subst_var e]
  | .prim _ ts => by simp [Term.subst, Terms.subst_var ts]
  | .effect _ ts => by simp [Term.subst, Terms.subst_var ts]
  | .freeImpure e => by simp [Term.subst, Term.subst_var e]
  | .freeBind v _ e => by simp [Term.subst, liftSub_var, Term.subst_var v, Term.subst_var e]

theorem Terms.subst_var {n : Nat} : (ts : Terms n) → ts.subst Term.var = ts
  | .nil => rfl
  | .cons t ts => by simp [Terms.subst, Term.subst_var t, Terms.subst_var ts]

theorem Arms.subst_var {n : Nat} : (as : Arms n) → as.subst Term.var = as
  | .nil => rfl
  | .cons _ b rest => by simp [Arms.subst, liftSub_var, Term.subst_var b, Arms.subst_var rest]

end

/-- Closed terms have no free variables. -/
theorem Term.freeVars_closed (t : Term 0) : t.freeVars = [] := by
  simp [Term.freeVars]

end Granule

end
