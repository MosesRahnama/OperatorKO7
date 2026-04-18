import OperatorKO7.Meta.MatrixBarrier2_Schema
import OperatorKO7.Meta.CompositionalMeasure_Impossibility

namespace OperatorKO7.MatrixBarrier2

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

/-- KO7 specialization of the tracked first-component dimension-2 barrier. -/
theorem no_global_step_orientation_matrix2_of_componentwise_pump
    (M : StepDuplicatingSchema.MatrixMeasure2 ko7Schema)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRange1 M) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval StepDuplicatingSchema.PairLt := by
  exact
    StepDuplicatingSchema.no_global_orients_matrix2_of_componentwise_pump
      (Sys := ko7System) M hunbounded

/-- KO7 successor-pump specialization. -/
theorem no_global_step_orientation_matrix2_of_succ_pump
    (M : StepDuplicatingSchema.MatrixMeasure2 ko7Schema)
    (h_succ_bias : 1 ≤ M.succ_bias1) (h_succ_scale : 1 ≤ M.succ_scale1) :
    ¬ (∀ {a b : Trace}, Step a b → StepDuplicatingSchema.PairLt (M.eval b) (M.eval a)) := by
  intro h
  have hdup :
      ∀ b s n : Trace,
        StepDuplicatingSchema.PairLt (M.eval (app s (recΔ b s n))) (M.eval (recΔ b s (delta n))) := by
    intro b s n
    exact h (Step.R_rec_succ b s n)
  exact
    StepDuplicatingSchema.no_matrix2_orients_dup_step_of_succ_pump
      (S := ko7Schema) M h_succ_bias h_succ_scale hdup

/-- KO7 wrap-pump specialization. -/
theorem no_global_step_orientation_matrix2_of_wrap_pump
    (M : StepDuplicatingSchema.MatrixMeasure2 ko7Schema)
    (h_wrap_bias : 1 ≤ M.wrap_const1 + M.wrap_right1 * M.c_base1) :
    ¬ (∀ {a b : Trace}, Step a b → StepDuplicatingSchema.PairLt (M.eval b) (M.eval a)) := by
  intro h
  have hdup :
      ∀ b s n : Trace,
        StepDuplicatingSchema.PairLt (M.eval (app s (recΔ b s n))) (M.eval (recΔ b s (delta n))) := by
    intro b s n
    exact h (Step.R_rec_succ b s n)
  exact
    StepDuplicatingSchema.no_matrix2_orients_dup_step_of_wrap_pump
      (S := ko7Schema) M h_wrap_bias hdup

end OperatorKO7.MatrixBarrier2
