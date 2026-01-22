/-!
Tiny smoke tests.

Why this file exists:
- Ensures the Lake package can compile a small `#eval` and a basic `#check` on a fresh machine.
- Keeps a minimal test surface under `OperatorKO7/Test/` to catch obvious toolchain regressions.
- This file is intentionally trivial and does not contribute to the KO7 theorems.
-/

#eval (1 + 1)
#check Prod.Lex
