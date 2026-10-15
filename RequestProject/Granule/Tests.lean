import RequestProject.Granule.Interpreter
import RequestProject.Granule.Theory

/-!
# Unit tests for the Granule port

Port of the interpreter-relevant hspec unit test (`Language.Granule.Syntax.ExprSpec`),
plus small checks of the parser, the well-scoped core and the pretty printer.
The golden tests over `.gr` files are run by the `granule-test` executable.
-/

namespace Granule.Tests

-- `ExprSpec`: free variables of `\x -> \y -> z` are `[z]`.
#guard SExpr.freeVars (.abs (.var "x") none (.abs (.var "y") none (.var "z"))) == ["z"]

-- Bound variables are scoped as de Bruijn `Fin` indices; a lambda's body lives in
-- `Term (0 + 1)`, and the closed term pretty prints back to source syntax.
#guard (match parseExpr "\\x -> \\y -> x" with
  | .ok e => e.toClosed.pretty
  | .error err => err) == "\\x -> \\y -> x"

/-- Free variables of a closed `Term 0` are always empty (`Term.freeVars_closed`). -/
example (t : Term 0) : t.freeVars = [] := Term.freeVars_closed t

/-- Renaming by the identity and substitution of variables are no-ops. -/
example {n : Nat} (t : Term n) : t.rename id = t ∧ t.subst Term.var = t :=
  ⟨Term.rename_id t, Term.subst_var t⟩

end Granule.Tests
