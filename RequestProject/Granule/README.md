# Granule in Lean

A Lean 4 port of the Granule front end (lexer, parser) and interpreter.

| File | Ports |
| --- | --- |
| `Syntax.lean` | surface AST (`Syntax/{Type,Pattern,Expr,Def}.hs`), `freeVars` |
| `Lexer.lean` | `Syntax/Lexer.x` (longest-match lexer) |
| `Parser.lean` | `Syntax/Parser.y` (recursive descent with the same precedences) |
| `Core.lean` | well-scoped core: `Pat k` binds `k` variables, `Term n` has variables `Fin n`; `Term 0` = closed terms; renaming and substitution |
| `Scope.lean` | named surface syntax → well-scoped `Term` |
| `Pretty.lean` | pretty printer (matches Haskell `show` for numbers, chars, strings) |
| `Eval.lean` | `interpreter/src/Language/Granule/Interpreter/Eval.hs` (CBV and CBN, builtins, channels, effects) |
| `Interpreter.lean` | `Interpreter.hs` driver (literate markdown, imports from `StdLib`, flags) |
| `Theory.lean` | proved laws: `rename_id`, `rename_rename`, `subst_var`, `freeVars_closed` |
| `Cli.lean` | executable `granule FILE...` |
| `Test.lean` | executable `granule-test`: golden tests over `examples`, `StdLib`, `frontend/tests/cases/positive` |
| `Tests.lean` | unit tests (`ExprSpec` port) checked at build time |

Run `lake build granule granule-test` then `lake test` (or `.lake/build/bin/granule-test`).

Not ported: the type checker (it relies on the Z3 SMT solver), the hole rewriter and the
program synthesiser, so the `negative`, `rewrite` and `synthesis` golden tests are not run.
`examples/Files.gr` and `examples/FilesBoxed.gr` read the repository's `LICENSE` file, which
is not present in this copy; with that file present they pass.
