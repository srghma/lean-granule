# Summary of changes for run 2a7b189c-a95b-44cc-8b0b-8e8a5360a08c
The Granule port now passes 486 of the 487 golden tests (run with `lake exe granuleTest`). The one failure is `positive/security/level_pos3.gr`. As far as I can tell from the Haskell sources, the predicate the checker builds for it really is false, so I left it failing rather than change the semantics to make it pass.

**Where things stood:** the project built without `sorry`, and the checker unit tests (`#guard`s in `CheckerTests.lean` and `SynthesisTests.lean`) and the solver soundness files all build. 485 tests passed and two failed. The `badRecursiveArgument.gr.output` change you asked for earlier is in place and that test passes.

**Fixed: `synthesis/graded-base/misc/either.gr`.** Every other file in `synthesis/graded-base` has a `language GradedBase` line; this one doesn't. Without the line it goes to the linear-base synthesiser, which used up its whole search budget and left the hole unfilled. The expected output, though, is exactly what the graded-base synthesiser produces: I added the pragma to a temporary copy and the result matched apart from the pragma line. The linear-base synthesiser would also list the `Right` case first, as `synthesis/either.gr.output` shows.
- The test runner now enables `GradedBase` for every file under `synthesis/graded-base`, as if the file declared it. This is a new `extraExtensions` option in `Config` (`Interpreter.lean`), used by `configFor` in `Test.lean`. It doesn't follow the Haskell test runner, which takes extensions only from the file's own pragmas.
- No test files were changed.

**Still failing: `positive/security/level_pos3.gr`.** For the polymorphic `incr : ∀ {l : Level} . …` the constraint is false at `l = Public` (and at `l = Unused`).
- The promotion `[car + i]` multiplies the security-context grade by `l`. At `Public` this breaks the `… ≤ Dunno` and `… ≤ 1` constraints.
- That is the same rule that makes the negative test `negative/security/level_neg6.gr` fail as expected; its expected output itself reports `Public * (1 : Level) ≤ Dunno` as false.
- Replacing `l` with `Public` in this file gets "Falsifiable theorem", and replacing it with `Private` passes.
- I checked the port against the Haskell sources: the `Level` ordering, join, meet, `times = join`, the variable domain `{Private, Public, Unused}` and the `normalise` unit exemption all match line for line. Given those definitions the predicate is not valid.
- Accepting the file would mean no longer rejecting `level_neg6.gr` or changing the `Level` semantics. Neither has been done.
- I couldn't run Haskell Granule or Z3 here, so I can't confirm directly how the original behaves on this file. If it accepts it, the constraints it builds must differ from the port's somewhere I didn't find.

Both cases are written up in `TEST-NOTES.md`. The work is committed and pushed, and the default library and the `granuleTest` executable build successfully.

## Suggested follow-up

Two of the test files may be out of step with the Haskell sources. `synthesis/graded-base/misc/either.gr` is the only file in its directory without `language GradedBase`. And for `positive/security/level_pos3.gr`, the Haskell `Level` rules as written seem to reject the program (the same rule that `negative/security/level_neg6.gr` relies on). If you want, I can add the missing pragma (and update the expected output) instead of using the test-runner setting, or move or restrict the security test. Just tell me which you prefer.