import OperatorKO7.Meta.MatrixBarrierD_Schema
import OperatorKO7.Meta.MatrixBarrierFunctional_Schema

/-!
# Explicit Matrix Projection Coverage

This module does not add a new obstruction mechanism. It names the two matrix-side
coverage patterns that matter operationally for automated tools:

- a fixed tracked row (already covered by `MatrixBarrierD`);
- a row-sum / all-ones projection (already covered by `MatrixBarrierFunctional`).

The purpose is to make those coverage points explicit in the artifact and in the paper's
TTT2 discussion, rather than leaving them implicit across several files.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-- All-ones projection used for row-sum coverage on `Fin d → Nat`. -/
def rowSumWeight {d : Nat} : Fin d → Nat := fun _ => 1

theorem rowSumWeight_support {d : Nat} (i : Fin d) :
    0 < rowSumWeight i := by
  simp [rowSumWeight]

/-- Fixed-row phrasing of the dimension-parametric tracked-component barrier. -/
theorem no_matrix_orients_dup_step_of_fixed_row_pump
    {S : StepDuplicatingSchema} {d : Nat} {tracked : Fin d}
    (M : MatrixMeasureD S d tracked)
    (hunbounded : HasUnboundedRangeTracked M) :
    ¬ (∀ (b s n : S.T),
      VecLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  exact no_matrixD_orients_dup_step_of_componentwise_pump M hunbounded

/-- Successor-pump fixed-row corollary. -/
theorem no_matrix_orients_dup_step_of_fixed_row_succ_pump
    {S : StepDuplicatingSchema} {d : Nat} {tracked : Fin d}
    (M : MatrixMeasureD S d tracked)
    (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale) :
    ¬ (∀ (b s n : S.T),
      VecLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  exact no_matrixD_orients_dup_step_of_succ_pump M h_succ_bias h_succ_scale

/-- Row-sum phrasing of the weighted functional barrier. The theorem is just the all-ones
instance of the general projection-based componentwise barrier. -/
theorem no_matrixFunctional_orients_dup_step_of_row_sum_pump
    {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixFunctionalMeasure S d)
    (hweight : M.weight = rowSumWeight)
    (hunbounded : HasUnboundedWeightedRange M) :
    ¬ (∀ (b s n : S.T),
      VecLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  have hM : M.weight = rowSumWeight := hweight
  exact no_matrixFunctional_orients_dup_step_of_componentwise_pump M (by
    simpa [hM] using hunbounded)

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
