# Summary of changes for run 271022ac-e02f-48b8-9280-413d8bdaa7d9
I ported the remaining synthesis features. The library and the `granule`, `grc` and `granuleTest` executables all build, and there is no `sorry` in the project. The golden tests give the same result as before: 486 of 487 pass. The one failure is still `positive/security/level_pos3.gr`. I traced it and it is not caused by the port: the Lean checker generates the same constraint Granule does, and that constraint is false. The upload has no `.known-issues` file, so I left it as it was (details in `TEST-NOTES.md`). Everything is committed and pushed.

**What was ported**
- **Cartesian synthesis (`--cart-synth`).** With `--cart-synth 1`, a candidate program is accepted only if it matches the graded program in `<file>.output`.
- **Synthesis benchmarking (`--benchmark`, `--raw-data`).** This prints solver call counts, timings, theorem sizes and paths explored, in both the human-readable and `Measurement` formats.
- **Search-tree output (`--synth-html`).** The rules used to build each program are recorded and written to an HTML file next to the source file.
- **Linear Haskell synthesis (`--linear-haskell`), in the new file `Synthesis/LinearHaskell.lean`.**
  - Granule reads Haskell with the `haskell-src-exts` library, so the port includes a small Haskell reader. It handles comments and pragmas, type signatures, `data` declarations (ordinary and GADT syntax) and equations.
  - The flow follows Granule: Haskell types become graded types (`->` is `Many`; `%1 ->`, `->.` and `⊸` are `One`; `% m ->` is `m`). The file is type-checked, each hole is synthesised, and the result is written back to the `.hs` file. If there is nothing to synthesise, it reports "Couldn't synthesise Linear Haskell..." and exits with code 1.
  - For example, `f :: a %1 -> a; f x = _` becomes `f x = x`, and `g :: Maybe a %1 -> Maybe a; g = _` becomes two equations, one for `Nothing` and one for `Just y`.
- **Interactive mode (`--interactive`).** As in Granule, synthesis has no limit and pauses at each failure until a line is entered.

**Differences from Granule** (also listed in `RequestProject/Granule/README.md`)
- **Linear Haskell output:** the rest of the file is left as it was, including comments and layout. Granule reprints the whole module.
- **`%1 ->`:** read as a linear arrow.
- **`f = e` equations:** if the definition is not rewritten, the equation is kept. Granule deletes it.
- **Granule's output bugs are reproduced as-is:**
  - constructor arguments in generated patterns come out reversed;
  - `x : xs` is printed as `[x]`, dropping the tail;
  - when the program found is a `case` on an argument, only its first branch is written.
- **Benchmark timings** measure the Lean solver.
- **The HTML page** has a different layout from Granule's.

**New tests** (run when the library is built)
- `RequestProject/Granule/LinearHaskellTests.lean`: type translation, declaration parsing and end-to-end synthesis on small Haskell files.
- `RequestProject/Granule/SynthesisOptionsTests.lean`: the new flags and synthesis options.

## Suggested follow-up

The three Linear Haskell output bugs listed above come from Granule's own code. They can produce Haskell that is wrong or ill-scoped, for example `either' e = Right x`, or `[x]` where `x : xs` was meant. I can fix them in the port if you'd prefer correct output over matching Granule exactly.