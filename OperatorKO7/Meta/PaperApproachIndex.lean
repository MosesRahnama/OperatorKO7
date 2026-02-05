import OperatorKO7.Meta.Impossibility_Lemmas

/-!
# Paper Approach Index (compile-time consistency check)

Purpose
- This module exists to make the paper’s “ten approaches fail” claim mechanically checkable.
- It provides *editor-quiet* references (`example` terms) to the specific approach namespaces/lemmas,
  so renames/deletions break compilation instead of silently drifting.

How to use
- Run: `lake build OperatorKO7.Meta.PaperApproachIndex`
- This is intentionally *not* imported by the default `OperatorKO7.lean` entrypoint, to keep the
  default build fast; treat it as an “audit target”.
-/

namespace OperatorKO7.Meta.PaperApproachIndex

open OperatorKO7 Trace
open OperatorKO7.Impossibility

/-!
Approach #9 and #10 were added later; keep explicit anchors here so the paper’s
“ten approaches” catalog stays in sync with the mechanized codebase.
-/

-- Approach #9: Complex Hybrid/Constellation Measures
example (b s n : Trace) :=
  ConstellationFailure.constellation_size_not_decreasing b s n

-- Approach #10: Unchecked Recursion
example (b s n : Trace) :=
  UncheckedRecursionFailure.rec_succ_additive_barrier b s n

example :=
  UncheckedRecursionFailure.full_step_permits_barrier

end OperatorKO7.Meta.PaperApproachIndex

