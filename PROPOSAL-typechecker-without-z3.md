# Proposal: type checker, hole rewriter and synthesiser for the Lean port, without Z3

## 1. What this is about

The Lean port runs every positive golden test (209 files) and the two negative
tests that fail during parsing. These parts are still not run:

| Suite | Files | What it needs |
|---|---|---|
| `frontend/tests/cases/negative` | 151 (2 already run) | type checker, and the grade solver in 62 of them |
| `frontend/tests/cases/rewrite` | 13 | type checker, hole case-splitting, reprinter |
| `frontend/tests/cases/synthesis` | 101 (the 9 `hilbert` files run in 3 modes) | type checker, synthesiser |
| `frontend/tests/hspec` unit tests | about 40 `it` cases | checker, kinding, substitution, synthesis internals |

In Haskell Granule, all three components call Z3 through SBV. This document
proposes how to port them to Lean with **no external SMT solver**. Z3 would be
replaced by a constraint solver written in Lean. Section 6 proposes proving it
sound in Lean.

## 2. What Z3 is used for

Every call goes through one function,
`Language.Granule.Checker.Constraints.provePredicate`:

```haskell
provePredicate :: Pred -> Ctxt (Type, Quantifier) -> Ctxt [Id] -> IO (Double, SolverResult)
data SolverResult = QED | NotValid String | NotValidTrivial [Constraint]
                  | Timeout | SolverProofError String | OtherSolverError String
```

There are 11 call sites: 6 in `Checker.hs` (checking definitions and
impossible patterns), 1 in `Synthesis/Common.hs` (checking candidate grades)
and 1 in `Synthesis/Splitting.hs` (removing impossible constructors when a hole
is split; for example, `head''` in `rewrite/head.gr` loses its `Nil` case
because `0 = n + 1` is unsatisfiable). The rest of the checker never talks to
the solver. So **the whole Z3 dependency is one interface**, and we can
implement that interface ourselves.

### 2.1 The input language

A `Pred` is built from `Conj`, `Disj`, `Impl` (with locally universally bound
variables), `NegPred`, `Exists` and atomic `Constraint`s:

```
Eq / Neq / ApproximatedBy (≤) / Lub / Hsup  over a grade type
Lt / Gt / LtEq / GtEq                       over Nat
```

The free variables are quantified by the context: `ForallQ` and `BoundQ` are
universal, `InstanceQ` is existential (∀∃ alternation does happen).

### 2.2 The theories behind each grade type (`SymbolicGrades.hs`)

| Granule grade type | SBV encoding | Proposed Lean encoding | How it is decided |
|---|---|---|---|
| `Nat` | `SInteger` with `≥ 0` | `Nat` / `Int` | Presburger arithmetic, plus a nonlinear layer (§4.4) |
| `Level` (Private/Public/Unused/Dunno) | `SInteger` from 0 to 3 | 4-value enum | try every value |
| `Sec` (Hi/Lo) | `SBool` | `Bool` | try every value |
| `LNL` (Zero/One/Many) | `SInteger` from 0 to 2 | 3-value enum | try every value |
| `OOZ` | `SBool` | `Bool` | try every value |
| `Cartesian` | unit | `Unit` | trivial |
| `Set a` / `SetOp a` | `SSet String` | `Finset` over the constructor names in scope | try every subset (the universe is finite: `?constructors`) |
| `Ext Nat` | `SNatX` (an integer, or ∞) | `Option Nat` | split each variable into finite or ∞, then use the `Nat` procedure |
| `Ext t` | (grade, isInf) | `t × Bool` | split on the flag, then use the procedure for `t` |
| `Interval t` | (lower, upper) with `lower ≤ upper` | pair | split into its two parts |
| `t₁ × t₂` | `SProduct` | pair | split into its two parts |
| `Q` | IEEE `SFloat` | `Rat` (see note) | linear rational arithmetic (Fourier–Motzkin or simplex) |
| `Fraction` / `Star` | `SFrac` (a real, or ★) | `Option Rat` | split, then linear rational arithmetic |
| polymorphic grade (`k : Coeffect`) | `SUnknown SynTree` with integer leaves | port `SynTree` as is | syntactic matching, leaving integer constraints on the leaves |

Note on `Q`: SBV uses IEEE floating point. Exact rationals give the same
answers on everything in the test suite (8 files mention `Q`), and they match
Granule's documented semantics better. The difference (no NaN, no rounding)
should be documented.

Because `Interval`, `Ext`, products and polymorphic grades all break down into
the base sorts, the solver core only needs **three procedures**: one for
finite sorts, one for integers and one for linear rationals.

## 3. Architecture

```
RequestProject/Granule/Checker/…           port of Language.Granule.Checker.* (named types, as in Haskell)
RequestProject/Granule/Solver/Formula.lean well-scoped formula language  Formula : Nat → Type
RequestProject/Granule/Solver/Compile.lean Pred + quantifier context → Formula 0   (replaces Constraints.hs)
RequestProject/Granule/Solver/Finite.lean  enumeration for finite sorts
RequestProject/Granule/Solver/Presburger.lean  Cooper / Omega quantifier elimination over ℤ
RequestProject/Granule/Solver/Poly.lean    polynomial normal form, nonlinear heuristics
RequestProject/Granule/Solver/LinRat.lean  Fourier–Motzkin over ℚ
RequestProject/Granule/Solver/Solve.lean   driver: provePredicate : Pred → … → IO SolverResult
RequestProject/Granule/Solver/Sound.lean   soundness theorems (§6)
```

The formula language follows the same design as `Term n` in the existing port.
Solver variables are de Bruijn indices `Fin n`, and a closed formula is
`Formula 0`:

```lean
inductive Sort where | int | bool | enum (k : Nat) | rat | set (universe : List String)
inductive Formula : Nat → Type where
  | tt | ff
  | atom   : Atom n → Formula n                 -- linear/polynomial (in)equalities, set membership, …
  | and | or | imp : Formula n → Formula n → Formula n
  | not    : Formula n → Formula n
  | all    : Sort → Formula (n+1) → Formula n
  | ex     : Sort → Formula (n+1) → Formula n
```

This makes `eval : Formula n → (Fin n → Value) → Prop` easy to state and gives
the soundness proofs in §6 a precise target. Variable names are kept on the
side (`Fin n → String`) only for printing counter-examples.

## 4. The solver

### 4.1 Simplification and trivial cases
Port `Checker/Simplifier.hs` and `trivialUnsatisfiableConstraints` exactly.
Many predicates are already decided at this stage, and the `NotValidTrivial`
messages (Grading error) come from here. They must match Haskell byte for byte.

### 4.2 Removing finite sorts
For variables of type `Level`, `Sec`, `LNL`, `OOZ` or `Set`, expand the
quantifier: `∀x. φ` becomes the conjunction of `φ[v/x]` over all values `v`,
and `∃` becomes the disjunction. The universes have at most 4 values, except
sets, where it is `2^|constructors used|`. In the test suite this is tiny. If
it grows, substitute values lazily and stop at the first failing case, which
also gives the counter-example.

### 4.3 Integer arithmetic: Presburger
After removing ∞ flags and finite sorts, most remaining goals are linear
integer arithmetic with ∀∃ alternation, for example
`∀ n m. ∃ k. k = n + m ∧ k ≤ …`. Presburger arithmetic is **decidable**:

* Implement **Cooper's quantifier elimination** (simple and complete, and it
  handles `∃` inside `∀`), or the **Omega test**. Both are a few hundred lines
  of Lean.
* Before that, use a cheap pre-pass: if an `InstanceQ` variable is defined by
  an equation `x = t`, substitute `t` for it. That covers nearly all
  existentials Granule produces (unification variables).
* Nat variables get `0 ≤ x` guards, as in `freshSolverVarScoped`.
* For counter-examples, eliminate the quantifiers of the *negated* formula and
  read back witnesses, or run a bounded search (below) once invalidity is known.

Lean's built-in `omega` is a tactic. It only proves universally quantified
goals, works at elaboration time and returns no models. That is why we
propose our own procedure, which runs inside the compiled checker.

### 4.4 Nonlinear integer terms (`n * m`, `r * s` in polymorphic code)
Z3 is incomplete here too, so the goal is to agree with Z3 on Granule's
corpus. Try these in order:

1. **Polynomial normal form** (sum of monomials with integer coefficients). An
   equality holds universally exactly when the normal forms are equal. Over
   `Nat`, `p ≤ q` holds universally if `q - p` has only non-negative
   coefficients (sound, and enough for typical grade goals such as
   `n * m ≤ n * m + 1`).
2. **Treat nonlinear monomials as fresh atoms** (`n*m ↦ a`) and run Presburger.
   This is sound for proving validity, because it only forgets information.
3. **Bounded search for a counter-example**: try assignments in a fixed order
   (by sum of absolute values, then by variable order) up to a bound such as
   0…16 per variable. Any falsifying assignment proves `NotValid`.
4. If all of these fail, return `OtherSolverError "unknown"` (Z3's "unknown"
   result). Granule already prints that as a solver error.

### 4.5 Linear rational arithmetic (`Q`, `Fraction`)
Use Fourier–Motzkin elimination over `Rat`. It is complete for linear
arithmetic over the rationals with quantifiers and easy to verify. The ★ case
of `Fraction` is a case split, like ∞.

### 4.6 Polymorphic grades (`SynTree`)
`SynTree.hs` is already a syntactic procedure: leaves are integers that stand
for `1 + … + 1`, and `synTreeApproxEq` produces integer equalities. Port it
directly. The integer side conditions then go to §4.3.

### 4.7 Timeouts
Granule's default limit is 10 s (`solverTimeoutMillis`). Replace it with a
fuel or step budget in the Lean solver (number of cases tried and quantifier
elimination steps), so results are deterministic. If the budget runs out,
return `Timeout`, which produces Granule's existing `SolverTimeout` error.

## 5. Matching the golden outputs

### 5.1 Messages that do not depend on the solver
"Falsifiable theorem" vs "Counter example" is **not** a solver choice. In
`Checker.hs:1872` the message is "Falsifiable theorem" when the falsifying
model has no variables, and "Counter example" otherwise. That follows from
the shape of the predicate, so we can reproduce it exactly. The predicate text
in messages (for example `(n0 = 0) ∧ (n0 > 0)`) comes from Granule's own
pretty-printer and **fresh-name generator**. The checker port must therefore
copy `freshIdentifierBase` and the order in which constraints are produced
exactly. This affects fidelity more than the solver does.

### 5.2 Concrete counter-example values (16 tests)
Sixteen negative outputs contain a model chosen by Z3, in SBV's format:

```
Counter-example:
  n = 15 :: Integer
  m =  3 :: Integer
```

(`flattenByLet`, `flattenNat`, `fact-inf`, `fixCounterExample`, `flat`,
`impossibilityCheck`, `polySemiring`, `polyShaped`,
`semiringsDontHaveCommutativeMult`, `universal`, `hsup/pushPair`,
`hsup/pushPolyLNL`, `badRecursiveArgument`, `everyOtherBroken`,
`everyOtherBroken2`, `impossiblePat`.)

These values depend on Z3's internal search (`n = 15, m = 3` is not a
"smallest" counter-example), so no other solver can be expected to reproduce
them. The options:

* **A (recommended): compare these outputs modulo the model.** The test runner
  compares everything outside the `Counter-example:` block byte for byte. For
  the block itself, it checks that the variable names, the order, the `:: type`
  suffixes and the layout match, and that the solver's own model really
  falsifies the predicate. The solver re-evaluates the predicate under its
  model, and the runner records that check. The values may differ. The `.output`
  files stay unchanged, and the runner reports these 16 tests as "passed
  (model differs from Z3)", so the gap is visible.
* B: regenerate the 16 `.output` files from the Lean solver. This is simpler,
  but it changes the user's reference data, so it is not recommended without
  explicit agreement.
* C: a per-test table of expected models. Rejected, because it fakes the result.

Either way, copy SBV's formatting exactly. The `=` signs line up, numbers are
right-aligned (`m =  3`), and `rewriteMessage` applies its text substitutions
(`Integer` becomes `Level` / `Private` / `Public`, or the kind name for
polymorphic grades, as in `r = 3 :: s`).

## 6. Proving the solver sound in Lean

Replacing Z3 with our own code is only an improvement if the code can be
trusted. Lean lets us prove it:

```lean
theorem solve_qed_sound   : solve φ = .qed            → ∀ ρ, φ.eval ρ        -- validity
theorem solve_cex_sound   : solve φ = .notValid model → ¬ φ.eval (model)     -- real counter-example
theorem cooper_correct    : (cooperQE φ).eval ρ ↔ φ.eval ρ
theorem finiteExpand_correct, polyNormal_correct, fm_correct, …
```

With `Formula : Nat → Type` and `eval`, each procedure is a function on
formulas that preserves meaning, which is exactly the kind of statement that
is practical to prove. Completeness is not needed, and is impossible for the
nonlinear part. A second step can relate `Compile.lean` to the semantics of
grades (resource algebras) already modelled in `Theory.lean`.

## 7. Porting the checker, hole rewriter and synthesiser

The solver is the new design work. The bulk of the work is a faithful port.

| Haskell module group | Lines | Notes |
|---|---|---|
| `Checker/Checker.hs` | 2483 | definitions, patterns, linearity, grading |
| `Checker/Kinding.hs`, `Types.hs`, `Substitution*.hs`, `Normalise.hs`, `TypeAliases.hs` | ~2900 | unification, kind inference |
| `Checker/Monad.hs` | 1166 | state, error type and **all error messages** |
| `Checker/Primitives.hs` | 836 | types of built-ins (the interpreter has their values already) |
| `Checker/Predicates.hs`, `Simplifier.hs`, `Coeffects.hs`, `Effects.hs`, `Flatten.hs` | ~1300 | constraint construction |
| `Checker/Patterns.hs`, `Exhaustivity.hs`, `DataTypes.hs`, `NameClash.hs`, `Ghost.hs` | ~900 | |
| `Synthesis/*` | ~5800 | `Synth.hs` + `SynthLinearBase.hs` + `Common.hs`; `LinearHaskell`/`Deriving` only where tests need them |
| `RewriteHoles.hs`, `Refactor.hs`, `Splitting.hs`, `Text/Reprinter.hs` | ~800 | source-preserving reprinting of case-split holes |

Design choices:

* **Keep the checker on the named surface syntax** (`Granule.Ty`, `SExpr`),
  like Haskell. Error messages print source names and fresh names (`n0`,
  `xs1`), so named terms make matching the golden output much easier. The
  well-scoped `Term n` stays the representation for evaluation, and closed
  `Term 0` remains the interpreter's input. The checker runs *before* the
  translation in `Scope.lean`.
* Spans: the current port drops spans, but every checker error starts with
  `file:line:col:`. The parser must start recording spans on expressions,
  patterns, types and definitions. This change is needed early.
* Write `Checker` as `StateT CheckerState (ExceptT (List CheckerError) IO)`, the
  same shape as Haskell's monad, so control flow (including several errors
  reported at once, as in `two-errors.gr`) carries over line by line.
* Synthesis calls the solver on every candidate. An in-process Lean solver
  avoids SBV's per-query process start-up, so it should not be slower than Z3
  on these small queries. The search order of `Synth.hs` must be kept exactly,
  because the golden outputs show the *first* program found.

## 8. Milestones (each one makes a measurable set of tests pass)

1. **Spans and checker skeleton**: keep running the 209 positive tests, now
   also type-checked, with the solver stubbed out (always `QED`). This is a
   regression guard: the checker must accept every positive program.
2. **Errors that do not need the solver**: unification, kinds, linearity,
   name clashes, patterns and arity (about 85 negative tests: every `.output`
   that does not contain "Falsifiable theorem" / "Counter example" / "Grading
   error").
3. **Solver v1**: finite sorts, `Ext`/`Interval` splitting and Presburger. Turn
   it on and the positive tests must still pass. Then the "Falsifiable
   theorem" (48) and "Grading error" outputs.
4. **Solver v2**: nonlinear layer, rationals, `SynTree`, counter-example
   formatting and comparison mode A, giving the 16 model-bearing tests.
   Negative suite done.
5. **Holes**: `RewriteHoles` + `Splitting` + reprinter, giving the 13 rewrite
   tests and `negative/holes`.
6. **Synthesis**: `Synth.hs` in additive mode, then the subtractive and
   additive-pruning modes for `hilbert`, giving the 101 + 2×9 synthesis runs.
7. **Unit tests**: port `hspec` cases as Lean tests, using `#guard`, or the
   test driver for cases that need IO.
8. **Soundness proofs** (§6). These can be done alongside milestones 3–4.

## 9. Risks

* **Fresh names and constraint order** in messages: the main source of small
  diffs. To reduce the risk, port `Checker/Monad.hs` and `Predicates.hs`
  without restructuring.
* **Nonlinear goals Z3 happens to solve** but our heuristics do not. These
  show up as `OtherSolverError` in specific tests and are handled one by one
  (for example, a better monomial ordering or a larger search bound). They
  never cause an unsound `QED`, because §6 rules that out.
* **Counter-example values** (§5.2) cannot match Z3's byte for byte. This is
  unavoidable without Z3, and the proposed comparison mode reports it openly.
* **Size**: about 12k lines of checker and 6k of synthesis to port. The solver
  core (§4) is estimated at 1.5–2.5k lines of Lean plus proofs.

## 10. Alternatives considered

* **Call another external solver (cvc5, or Z3 via a binding)**: excluded,
  because the requirement is to avoid installing an SMT solver.
* **Use Lean's own `omega` / `decide` / `grind` at run time** by building a
  `MetaM` environment inside the executable. This is possible, but each run
  then needs Lean's `.olean` files at run time, starts slowly, cannot handle `∃`
  under `∀`, and produces no counter-examples. Some ideas can still be reused
  (`omega`'s normalisation) when writing §4.3.
* **Bounded checking only** (search for counter-examples up to N and otherwise
  report QED): rejected, because it is unsound. It could accept ill-graded
  programs.
