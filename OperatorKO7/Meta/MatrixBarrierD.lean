import OperatorKO7.Meta.CompositionalMeasure_Impossibility

/-!
# Dimension-Parametric Componentwise Matrix Barrier

This module generalizes the tracked-component componentwise barrier from dimension `2` to
arbitrary fixed finite dimension.

The proof remains deliberately modest: if one tracked coordinate already satisfies the scalar
affine barrier hypotheses, then strict componentwise decrease is impossible, because it would
force strict decrease in that coordinate.

This is a dimension-parametric extension of the tracked-component barrier, not a full theorem
about arbitrary mixed matrix interpretations.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-- Strict componentwise order on `Fin d → Nat` vectors. -/
def VecLt {d : Nat} (u v : Fin d → Nat) : Prop :=
  ∀ i : Fin d, u i < v i

/-- A finite-dimensional matrix-style measure with one tracked affine coordinate. -/
structure MatrixMeasureD (S : StepDuplicatingSchema) (d : Nat) (tracked : Fin d) where
  eval : S.T → Fin d → Nat
  c_base : Nat
  succ_bias : Nat
  succ_scale : Nat
  wrap_const : Nat
  wrap_left : Nat
  wrap_right : Nat
  recur_const : Nat
  recur_base : Nat
  recur_step : Nat
  recur_counter : Nat
  eval_base : eval S.base tracked = c_base
  eval_succ :
    ∀ t, eval (S.succ t) tracked = succ_bias + succ_scale * eval t tracked
  eval_wrap :
    ∀ x y,
      eval (S.wrap x y) tracked =
        wrap_const + wrap_left * eval x tracked + wrap_right * eval y tracked
  eval_recur :
    ∀ b s n,
      eval (S.recur b s n) tracked =
        recur_const + recur_base * eval b tracked +
          recur_step * eval s tracked + recur_counter * eval n tracked
  h_wrap_left_pos : 1 ≤ wrap_left
  h_wrap_right_pos : 1 ≤ wrap_right

/-- Project the tracked coordinate to the scalar affine barrier infrastructure. -/
def MatrixMeasureD.trackedAffine
    {S : StepDuplicatingSchema} {d : Nat} {tracked : Fin d}
    (M : MatrixMeasureD S d tracked) : AffineMeasure S where
  eval := fun t => M.eval t tracked
  c_base := M.c_base
  succ_bias := M.succ_bias
  succ_scale := M.succ_scale
  wrap_const := M.wrap_const
  wrap_left := M.wrap_left
  wrap_right := M.wrap_right
  recur_const := M.recur_const
  recur_base := M.recur_base
  recur_step := M.recur_step
  recur_counter := M.recur_counter
  eval_base := M.eval_base
  eval_succ := M.eval_succ
  eval_wrap := M.eval_wrap
  eval_recur := M.eval_recur
  h_wrap_left_pos := M.h_wrap_left_pos
  h_wrap_right_pos := M.h_wrap_right_pos

/-- Unbounded pump in the tracked coordinate. -/
def HasUnboundedRangeTracked
    {S : StepDuplicatingSchema} {d : Nat} {tracked : Fin d}
    (M : MatrixMeasureD S d tracked) : Prop :=
  ∀ k : Nat, ∃ t : S.T, k ≤ M.eval t tracked

/-- A tracked affine failure already rules out strict componentwise orientation in any
fixed finite dimension. -/
theorem no_matrixD_orients_dup_step_of_componentwise_pump
    {S : StepDuplicatingSchema} {d : Nat} {tracked : Fin d}
    (M : MatrixMeasureD S d tracked)
    (hunbounded : HasUnboundedRangeTracked M) :
    ¬ (∀ (b s n : S.T),
      VecLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  have htracked :
      ∀ (b s n : S.T),
        M.eval (S.wrap s (S.recur b s n)) tracked <
          M.eval (S.recur b s (S.succ n)) tracked := by
    intro b s n
    exact h b s n tracked
  have hunbounded' : HasUnboundedRange M.trackedAffine := by
    intro k
    rcases hunbounded k with ⟨t, ht⟩
    exact ⟨t, ht⟩
  exact
    no_affine_orients_dup_step_of_unbounded
      (S := S) M.trackedAffine hunbounded' htracked

/-- Successor-pump corollary for the tracked coordinate. -/
theorem no_matrixD_orients_dup_step_of_succ_pump
    {S : StepDuplicatingSchema} {d : Nat} {tracked : Fin d}
    (M : MatrixMeasureD S d tracked)
    (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale) :
    ¬ (∀ (b s n : S.T),
      VecLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  have htracked :
      ∀ (b s n : S.T),
        M.eval (S.wrap s (S.recur b s n)) tracked <
          M.eval (S.recur b s (S.succ n)) tracked := by
    intro b s n
    exact h b s n tracked
  exact
    no_affine_orients_dup_step_of_succ_pump
      (S := S) M.trackedAffine h_succ_bias h_succ_scale htracked

/-- Wrap-pump corollary for the tracked coordinate. -/
theorem no_matrixD_orients_dup_step_of_wrap_pump
    {S : StepDuplicatingSchema} {d : Nat} {tracked : Fin d}
    (M : MatrixMeasureD S d tracked)
    (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base) :
    ¬ (∀ (b s n : S.T),
      VecLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  have htracked :
      ∀ (b s n : S.T),
        M.eval (S.wrap s (S.recur b s n)) tracked <
          M.eval (S.recur b s (S.succ n)) tracked := by
    intro b s n
    exact h b s n tracked
  exact
    no_affine_orients_dup_step_of_wrap_pump
      (S := S) M.trackedAffine h_wrap_bias htracked

/-- The tracked-component componentwise barrier also lifts to global root orientation. -/
theorem no_global_orients_matrixD_of_componentwise_pump
    {Sys : StepDuplicatingSystem} {d : Nat} {tracked : Fin d}
    (M : MatrixMeasureD Sys.toStepDuplicatingSchema d tracked)
    (hunbounded : HasUnboundedRangeTracked M) :
    ¬ GlobalOrients Sys M.eval VecLt := by
  intro h
  exact
    no_matrixD_orients_dup_step_of_componentwise_pump
      (S := Sys.toStepDuplicatingSchema) M hunbounded
      (fun b s n => h (Sys.dup_step b s n))

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating

namespace OperatorKO7.MatrixBarrierD

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

/-- KO7 specialization of the tracked fixed-dimension componentwise barrier. -/
theorem no_global_step_orientation_matrixD_of_componentwise_pump
    {d : Nat} (tracked : Fin d)
    (M : StepDuplicatingSchema.MatrixMeasureD ko7Schema d tracked)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRangeTracked M) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval StepDuplicatingSchema.VecLt := by
  exact
    StepDuplicatingSchema.no_global_orients_matrixD_of_componentwise_pump
      (Sys := ko7System) M hunbounded

/-- KO7 successor-pump specialization. -/
theorem no_global_step_orientation_matrixD_of_succ_pump
    {d : Nat} (tracked : Fin d)
    (M : StepDuplicatingSchema.MatrixMeasureD ko7Schema d tracked)
    (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale) :
    ¬ (∀ {a b : Trace}, Step a b → StepDuplicatingSchema.VecLt (M.eval b) (M.eval a)) := by
  intro h
  have hdup :
      ∀ b s n : Trace,
        StepDuplicatingSchema.VecLt (M.eval (app s (recΔ b s n))) (M.eval (recΔ b s (delta n))) := by
    intro b s n
    exact h (Step.R_rec_succ b s n)
  exact
    StepDuplicatingSchema.no_matrixD_orients_dup_step_of_succ_pump
      (S := ko7Schema) M h_succ_bias h_succ_scale hdup

/-- KO7 wrap-pump specialization. -/
theorem no_global_step_orientation_matrixD_of_wrap_pump
    {d : Nat} (tracked : Fin d)
    (M : StepDuplicatingSchema.MatrixMeasureD ko7Schema d tracked)
    (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base) :
    ¬ (∀ {a b : Trace}, Step a b → StepDuplicatingSchema.VecLt (M.eval b) (M.eval a)) := by
  intro h
  have hdup :
      ∀ b s n : Trace,
        StepDuplicatingSchema.VecLt (M.eval (app s (recΔ b s n))) (M.eval (recΔ b s (delta n))) := by
    intro b s n
    exact h (Step.R_rec_succ b s n)
  exact
    StepDuplicatingSchema.no_matrixD_orients_dup_step_of_wrap_pump
      (S := ko7Schema) M h_wrap_bias hdup

end OperatorKO7.MatrixBarrierD
