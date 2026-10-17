# Notes on the golden tests

Run with `lake exe granuleTest` from the repository root. Result: 486 of 487
tests pass.

## `synthesis/graded-base/misc/either.gr`

This file has no `language GradedBase` line. Every other file in
`synthesis/graded-base` has one. Its expected output, though, is what the
graded-base synthesiser produces:

* the patterns are in constructor order (`Left` first, then `Right`), and
* the names are `u` and `p`.

The linear-base synthesiser, which a file without the pragma would get, puts
the last constructor first (see `synthesis/either.gr.output`). On this file it
also runs out of its search budget, because an application loop never
terminates. So the test runner turns on `GradedBase` for every file under
`synthesis/graded-base`, as if the file declared it (`configFor` in
`RequestProject/Granule/Test.lean`). No test file was changed.

## `positive/security/level_pos3.gr` (still failing)

```
incr : ∀ { l : Level } . Int [l] → List (Int [l]) → List (Int [l])
incr [i] Nil = Nil;
incr [i] (Cons [car] cdr) = Cons [car + i] (incr [i] cdr)
```

The checker produces a grading constraint that is false when `l = Public`,
and also when `l = Unused`. The cause is the promotion `[car + i]` at level
`l`. It multiplies the ghost (security-context) grade by `l`, so the ghost
usage becomes `Public`. The constraints `… ≤ Dunno` and `… ≤ (1 : Level)` then
fail.

The same rule makes the negative test `negative/security/level_neg6.gr` fail
as expected: its expected output reports `Public * (1 : Level) ≤ Dunno` as
false. If you replace `l` by `Public` in `level_pos3.gr`, the port rejects
the program with "Falsifiable theorem", and replacing it by `Private` makes
it pass.

The symbolic encodings of `Level` match the Haskell sources line for line:

* the ordering, join, meet, `times = join`,
* the domain `{Private, Public, Unused}` of a `Level` variable,
* the unit exemption in `normalise`.

Given these definitions, the predicate is not valid. The port cannot accept
this program unless it also stops rejecting `level_neg6.gr` or changes the
`Level` semantics. Neither has been done.
