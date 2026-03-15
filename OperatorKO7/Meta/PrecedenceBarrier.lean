import OperatorKO7.Meta.Conjecture_Boundary

/-!
# Pure Head-Precedence Barrier

This module upgrades the standalone head-precedence witness to a theorem-backed family.
The family is intentionally narrow: the measure depends only on the head constructor.
-/

namespace OperatorKO7.PrecedenceBarrier

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.MetaConjectureBoundary

/-- Pure head-precedence measures: a term is ranked solely by its outermost constructor. -/
structure HeadPrecedenceFamily where
  rank : OpHead → Nat

/-- Evaluation for the pure head-precedence family. -/
def HeadPrecedenceFamily.eval (M : HeadPrecedenceFamily) : Trace → Nat :=
  headPrecedenceMeasure M.rank

/-- No pure head-precedence family can globally orient `Step`. The failure already appears
at the collapsing `merge_cancel` branch. -/
theorem no_global_step_orientation_headPrecedenceFamily (M : HeadPrecedenceFamily) :
    ¬ GlobalOrients M.eval (· < ·) := by
  simpa [HeadPrecedenceFamily.eval] using
    no_global_step_orientation_headPrecedence M.rank

end OperatorKO7.PrecedenceBarrier
