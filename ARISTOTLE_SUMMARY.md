# Summary of changes for run 40765f31-d22e-4db7-bb87-393d332969c3
I wrote the proposal in `PROPOSAL-typechecker-without-z3.md` at the project root. It's a design document only: no checker, solver or synthesiser code was written, and no Lean files changed.

**Main idea.** In the Haskell sources, every use of Z3 goes through one function, `provePredicate`. It has 11 call sites: in the checker, in synthesis, and in hole splitting. So Z3 can be replaced by a constraint solver written in Lean behind that same interface. The solver's formulas use the same design as `Term n`: variables are `Fin n` indices and a closed formula is `Formula 0`.

**How the solver would work:**
- **Finite grade types** (`Level`, `Sec`, `LNL`, `OOZ`, `Set`): try every possible value.
- **Composite grades** (`Ext Nat`, `Ext t`, `Interval`, products): split into parts and handle each part.
- **Linear integer arithmetic** (Presburger arithmetic, including ∀∃ quantifiers): a complete decision procedure (Cooper's algorithm or the Omega test).
- **Nonlinear integer terms** such as `n * m`: polynomial normal forms, then treating products as fresh unknowns, then a bounded search for counter-examples. If none of these settles it, the result is "unknown", never an unsound "proved".
- **`Q` and `Fraction`**: exact rational arithmetic (Fourier–Motzkin elimination). This differs slightly from Z3's IEEE floats, and the document says so.
- **Polymorphic grades** (`SynTree`): ported directly.
- **Timeouts**: replaced by a step budget, so results are deterministic.

It also proposes proving the solver sound in Lean: if the solver says "proved", the formula really holds, and any counter-example it returns really falsifies the formula.

**Matching the expected outputs.**
- 62 negative tests depend on the solver.
- Whether the message says "Falsifiable theorem" or "Counter example" follows from the shape of the constraint, not from Z3, so it can be reproduced exactly.
- 16 tests print the specific values Z3 happened to choose (for example `n = 15, m = 3`). No other solver can be expected to reproduce those. I recommend comparing these 16 outputs byte for byte except for the values, checking that our values really are a counter-example, and reporting them separately as "model differs from Z3". The alternative would mean rewriting your `.output` files, which I don't recommend without your agreement.

**Plan for the rest of the port.** The document covers:
- the Haskell modules to port, with line counts: about 12k lines of checker and about 6k of synthesis;
- keeping the checker on the named syntax, as in Haskell, so error messages and generated names like `n0` match;
- the parser starting to record source positions, since every checker error prints `file:line:col`;
- eight milestones, each tied to a set of tests that should then pass;
- risks, and alternatives I rejected: another external solver, running Lean's own `omega` at run time, and checking only up to a bound, which would be unsound.

The file is committed and pushed.