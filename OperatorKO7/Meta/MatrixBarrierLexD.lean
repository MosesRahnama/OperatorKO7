import OperatorKO7.Meta.MatrixBarrierLexD_Schema
import OperatorKO7.Meta.CompositionalMeasure_Impossibility

namespace OperatorKO7.MatrixBarrierLexD

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

/-- KO7 specialization of the finite tracked-primary lexicographic barrier. -/
theorem no_global_step_orientation_matrixLexD_of_unbounded_primary
    {d : Nat} (M : StepDuplicatingSchema.MatrixLexMeasureD ko7Schema d)
    (hunbounded : StepDuplicatingSchema.HasUnboundedPrimaryRange M) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval StepDuplicatingSchema.VecLexLt := by
  exact
    StepDuplicatingSchema.no_global_orients_matrixLexD_of_unbounded_primary
      (Sys := ko7System) M hunbounded

/-- KO7 successor-pump specialization for finite tracked-primary lexicographic families. -/
theorem no_global_step_orientation_matrixLexD_of_succ_pump
    {d : Nat} (M : StepDuplicatingSchema.MatrixLexMeasureD ko7Schema d)
    (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale) :
    ¬ (∀ {a b : Trace}, Step a b → StepDuplicatingSchema.VecLexLt (M.eval b) (M.eval a)) := by
  intro h
  have hdup :
      ∀ b s n : Trace,
        StepDuplicatingSchema.VecLexLt (M.eval (app s (recΔ b s n))) (M.eval (recΔ b s (delta n))) := by
    intro b s n
    exact h (Step.R_rec_succ b s n)
  exact
    StepDuplicatingSchema.no_matrixLexD_orients_dup_step_of_succ_pump
      (S := ko7Schema) M h_succ_bias h_succ_scale hdup

/-- KO7 wrap-pump specialization for finite tracked-primary lexicographic families. -/
theorem no_global_step_orientation_matrixLexD_of_wrap_pump
    {d : Nat} (M : StepDuplicatingSchema.MatrixLexMeasureD ko7Schema d)
    (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base) :
    ¬ (∀ {a b : Trace}, Step a b → StepDuplicatingSchema.VecLexLt (M.eval b) (M.eval a)) := by
  intro h
  have hdup :
      ∀ b s n : Trace,
        StepDuplicatingSchema.VecLexLt (M.eval (app s (recΔ b s n))) (M.eval (recΔ b s (delta n))) := by
    intro b s n
    exact h (Step.R_rec_succ b s n)
  exact
    StepDuplicatingSchema.no_matrixLexD_orients_dup_step_of_wrap_pump
      (S := ko7Schema) M h_wrap_bias hdup

/-- KO7 unconditional specialization for the strengthened finite lexicographic subclass. -/
theorem no_global_step_orientation_matrixLexD_with_primary_pump
    {d : Nat} (M : StepDuplicatingSchema.MatrixLexMeasureDWithPrimaryPump ko7Schema d) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval StepDuplicatingSchema.VecLexLt := by
  exact
    StepDuplicatingSchema.no_global_orients_matrixLexD_with_primary_pump
      (Sys := ko7System) M

end OperatorKO7.MatrixBarrierLexD
