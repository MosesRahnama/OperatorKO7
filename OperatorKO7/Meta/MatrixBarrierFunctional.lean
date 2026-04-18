import OperatorKO7.Meta.MatrixBarrierFunctional_Schema
import OperatorKO7.Meta.CompositionalMeasure_Impossibility

namespace OperatorKO7.MatrixBarrierFunctional

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

/-- KO7 specialization of the weighted componentwise projection barrier. -/
theorem no_global_step_orientation_matrixFunctional_of_componentwise_pump
    {d : Nat} (M : StepDuplicatingSchema.MatrixFunctionalMeasure ko7Schema d)
    (hunbounded : StepDuplicatingSchema.HasUnboundedWeightedRange M) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval StepDuplicatingSchema.VecLt := by
  exact
    StepDuplicatingSchema.no_global_orients_matrixFunctional_of_componentwise_pump
      (Sys := ko7System) M hunbounded

/-- KO7 successor-pump specialization for weighted componentwise projections. -/
theorem no_global_step_orientation_matrixFunctional_of_succ_pump
    {d : Nat} (M : StepDuplicatingSchema.MatrixFunctionalMeasure ko7Schema d)
    (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale) :
    ¬ (∀ {a b : Trace}, Step a b → StepDuplicatingSchema.VecLt (M.eval b) (M.eval a)) := by
  intro h
  have hdup :
      ∀ b s n : Trace,
        StepDuplicatingSchema.VecLt (M.eval (app s (recΔ b s n))) (M.eval (recΔ b s (delta n))) := by
    intro b s n
    exact h (Step.R_rec_succ b s n)
  exact
    StepDuplicatingSchema.no_matrixFunctional_orients_dup_step_of_succ_pump
      (S := ko7Schema) M h_succ_bias h_succ_scale hdup

/-- KO7 wrap-pump specialization for weighted componentwise projections. -/
theorem no_global_step_orientation_matrixFunctional_of_wrap_pump
    {d : Nat} (M : StepDuplicatingSchema.MatrixFunctionalMeasure ko7Schema d)
    (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base) :
    ¬ (∀ {a b : Trace}, Step a b → StepDuplicatingSchema.VecLt (M.eval b) (M.eval a)) := by
  intro h
  have hdup :
      ∀ b s n : Trace,
        StepDuplicatingSchema.VecLt (M.eval (app s (recΔ b s n))) (M.eval (recΔ b s (delta n))) := by
    intro b s n
    exact h (Step.R_rec_succ b s n)
  exact
    StepDuplicatingSchema.no_matrixFunctional_orients_dup_step_of_wrap_pump
      (S := ko7Schema) M h_wrap_bias hdup

end OperatorKO7.MatrixBarrierFunctional
