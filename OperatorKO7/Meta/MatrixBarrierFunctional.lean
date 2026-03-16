import OperatorKO7.Meta.MatrixBarrierD
import OperatorKO7.Meta.MatrixBarrierMix2

/-!
# Positive-Functional Matrix Barrier

This module unifies the tracked-coordinate and balanced-sum matrix barriers through
a fixed scalar projection. A vector-valued direct measure may use arbitrary finite
dimension, but if a nonzero natural-weighted projection of that measure satisfies
the scalar affine barrier interface, then strict componentwise orientation of the
duplicating step is impossible.

This still does not cover arbitrary matrix orders or arbitrary mixed-coordinate
interpretations. The theorem remains a projection barrier. Its value is that one
proof now covers tracked single-coordinate projections, aggregate-sum projections,
and any other fixed nonzero natural-weighted scalar projection whose constructor laws
factor through the affine interface.
-/

open scoped BigOperators

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

open Finset

/-- Fixed natural-weighted scalar projection on `Fin d → Nat`. -/
@[simp] def weightedSum {d : Nat} (weight : Fin d → Nat) (v : Fin d → Nat) : Nat :=
  ∑ i, weight i * v i

/-- A finite-dimensional componentwise matrix-style measure whose chosen scalar projection
is affine. The full coordinate laws are intentionally not axiomatized: only the projected
scalar interface matters for the barrier proof. -/
structure MatrixFunctionalMeasure (S : StepDuplicatingSchema) (d : Nat) where
  eval : S.T → Fin d → Nat
  weight : Fin d → Nat
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
  eval_base : weightedSum weight (eval S.base) = c_base
  eval_succ :
    ∀ t,
      weightedSum weight (eval (S.succ t)) =
        succ_bias + succ_scale * weightedSum weight (eval t)
  eval_wrap :
    ∀ x y,
      weightedSum weight (eval (S.wrap x y)) =
        wrap_const + wrap_left * weightedSum weight (eval x) +
          wrap_right * weightedSum weight (eval y)
  eval_recur :
    ∀ b s n,
      weightedSum weight (eval (S.recur b s n)) =
        recur_const + recur_base * weightedSum weight (eval b) +
          recur_step * weightedSum weight (eval s) +
          recur_counter * weightedSum weight (eval n)
  h_weight_support : ∃ i : Fin d, 1 ≤ weight i
  h_wrap_left_pos : 1 ≤ wrap_left
  h_wrap_right_pos : 1 ≤ wrap_right

/-- Project the chosen weighted scalar to the existing scalar affine barrier interface. -/
def MatrixFunctionalMeasure.projectedAffine
    {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixFunctionalMeasure S d) : AffineMeasure S where
  eval := fun t => weightedSum M.weight (M.eval t)
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

/-- Unbounded pump in the weighted scalar projection. -/
def HasUnboundedWeightedRange
    {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixFunctionalMeasure S d) : Prop :=
  ∀ k : Nat, ∃ t : S.T, k ≤ weightedSum M.weight (M.eval t)

/-- Strict componentwise decrease implies strict decrease of any nonzero natural-weighted
projection. -/
theorem weightedSum_lt_of_vecLt
    {d : Nat} {weight u v : Fin d → Nat}
    (hsupport : ∃ i : Fin d, 1 ≤ weight i)
    (h : VecLt u v) :
    weightedSum weight u < weightedSum weight v := by
  classical
  rcases hsupport with ⟨i0, hi0⟩
  have hmain : weight i0 * u i0 < weight i0 * v i0 := by
    exact Nat.mul_lt_mul_of_pos_left (h i0) (lt_of_lt_of_le Nat.zero_lt_one hi0)
  have hrest :
      ∑ j ∈ univ.erase i0, weight j * u j ≤
        ∑ j ∈ univ.erase i0, weight j * v j := by
    exact sum_le_sum (fun j _ => Nat.mul_le_mul_left _ (Nat.le_of_lt (h j)))
  have hu :
      weightedSum weight u =
        weight i0 * u i0 + ∑ j ∈ univ.erase i0, weight j * u j := by
    simpa [weightedSum, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (Finset.sum_erase_add (s := univ) (f := fun i => weight i * u i) (a := i0) (by simp)).symm
  have hv :
      weightedSum weight v =
        weight i0 * v i0 + ∑ j ∈ univ.erase i0, weight j * v j := by
    simpa [weightedSum, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (Finset.sum_erase_add (s := univ) (f := fun i => weight i * v i) (a := i0) (by simp)).symm
  rw [hu, hv]
  exact Nat.add_lt_add_of_lt_of_le hmain hrest

/-- A weighted affine failure already rules out strict componentwise orientation. -/
theorem no_matrixFunctional_orients_dup_step_of_componentwise_pump
    {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixFunctionalMeasure S d)
    (hunbounded : HasUnboundedWeightedRange M) :
    ¬ (∀ (b s n : S.T),
      VecLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  have hproj :
      ∀ (b s n : S.T),
        weightedSum M.weight (M.eval (S.wrap s (S.recur b s n))) <
          weightedSum M.weight (M.eval (S.recur b s (S.succ n))) := by
    intro b s n
    exact weightedSum_lt_of_vecLt M.h_weight_support (h b s n)
  have hunbounded' : HasUnboundedRange M.projectedAffine := by
    intro k
    rcases hunbounded k with ⟨t, ht⟩
    exact ⟨t, ht⟩
  exact
    no_affine_orients_dup_step_of_unbounded
      (S := S) M.projectedAffine hunbounded' hproj

/-- Successor-pump corollary for weighted scalar projections. -/
theorem no_matrixFunctional_orients_dup_step_of_succ_pump
    {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixFunctionalMeasure S d)
    (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale) :
    ¬ (∀ (b s n : S.T),
      VecLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  have hproj :
      ∀ (b s n : S.T),
        weightedSum M.weight (M.eval (S.wrap s (S.recur b s n))) <
          weightedSum M.weight (M.eval (S.recur b s (S.succ n))) := by
    intro b s n
    exact weightedSum_lt_of_vecLt M.h_weight_support (h b s n)
  exact
    no_affine_orients_dup_step_of_succ_pump
      (S := S) M.projectedAffine h_succ_bias h_succ_scale hproj

/-- Wrap-pump corollary for weighted scalar projections. -/
theorem no_matrixFunctional_orients_dup_step_of_wrap_pump
    {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixFunctionalMeasure S d)
    (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base) :
    ¬ (∀ (b s n : S.T),
      VecLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  have hproj :
      ∀ (b s n : S.T),
        weightedSum M.weight (M.eval (S.wrap s (S.recur b s n))) <
          weightedSum M.weight (M.eval (S.recur b s (S.succ n))) := by
    intro b s n
    exact weightedSum_lt_of_vecLt M.h_weight_support (h b s n)
  exact
    no_affine_orients_dup_step_of_wrap_pump
      (S := S) M.projectedAffine h_wrap_bias hproj

/-- Global componentwise orientation would orient the duplicating step as well. -/
theorem no_global_orients_matrixFunctional_of_componentwise_pump
    {Sys : StepDuplicatingSystem} {d : Nat}
    (M : MatrixFunctionalMeasure Sys.toStepDuplicatingSchema d)
    (hunbounded : HasUnboundedWeightedRange M) :
    ¬ GlobalOrients Sys M.eval VecLt := by
  intro h
  exact
    no_matrixFunctional_orients_dup_step_of_componentwise_pump
      (S := Sys.toStepDuplicatingSchema) M hunbounded
      (fun b s n => h (Sys.dup_step b s n))

/-- The tracked-coordinate family is an instance of the functional projection barrier,
using the singleton weight vector on the tracked coordinate. -/
def MatrixMeasureD.toFunctional
    {S : StepDuplicatingSchema} {d : Nat} {tracked : Fin d}
    (M : MatrixMeasureD S d tracked) : MatrixFunctionalMeasure S d where
  eval := M.eval
  weight := fun i => if i = tracked then 1 else 0
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
  eval_base := by
    simp [weightedSum, M.eval_base]
  eval_succ := by
    intro t
    simp [weightedSum, M.eval_succ]
  eval_wrap := by
    intro x y
    simp [weightedSum, M.eval_wrap]
  eval_recur := by
    intro b s n
    simp [weightedSum, M.eval_recur]
  h_weight_support := ⟨tracked, by simp⟩
  h_wrap_left_pos := M.h_wrap_left_pos
  h_wrap_right_pos := M.h_wrap_right_pos

/-- Re-derive the tracked-coordinate barrier from the functional theorem. -/
theorem no_matrixD_orients_dup_step_of_componentwise_pump_via_functional
    {S : StepDuplicatingSchema} {d : Nat} {tracked : Fin d}
    (M : MatrixMeasureD S d tracked)
    (hunbounded : HasUnboundedRangeTracked M) :
    ¬ (∀ (b s n : S.T),
      VecLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  apply no_matrixFunctional_orients_dup_step_of_componentwise_pump (M := M.toFunctional)
  intro k
  rcases hunbounded k with ⟨t, ht⟩
  exact ⟨t, by simpa [MatrixMeasureD.toFunctional, weightedSum] using ht⟩

/-- Convert a pair to a `Fin 2 → Nat` vector. -/
@[simp] def vec2ToFin (v : Vec2) : Fin 2 → Nat
  | ⟨0, _⟩ => v.1
  | ⟨1, _⟩ => v.2

/-- All-ones projection on pairs recovers the coordinate sum. -/
lemma weightedSum_vec2ToFin_ones (v : Vec2) :
    weightedSum (fun _ : Fin 2 => 1) (vec2ToFin v) = vecSum v := by
  simp [weightedSum, vec2ToFin, vecSum]

/-- The balanced mixed-coordinate family is also an instance of the functional barrier,
using the all-ones weight vector. -/
def MatrixMix2Measure.toFunctional
    {S : StepDuplicatingSchema}
    (M : MatrixMix2Measure S) : MatrixFunctionalMeasure S 2 where
  eval := fun t => vec2ToFin (M.eval t)
  weight := fun _ => 1
  c_base := vecSum M.c_base
  succ_bias := vecSum M.succ_bias
  succ_scale := M.succ_mat.sumCoeff
  wrap_const := vecSum M.wrap_bias
  wrap_left := M.wrap_left.sumCoeff
  wrap_right := M.wrap_right.sumCoeff
  recur_const := vecSum M.recur_bias
  recur_base := M.recur_base.sumCoeff
  recur_step := M.recur_step.sumCoeff
  recur_counter := M.recur_counter.sumCoeff
  eval_base := by
    rw [weightedSum_vec2ToFin_ones]
    simpa [vecSum] using congrArg vecSum M.eval_base
  eval_succ := by
    intro t
    rw [weightedSum_vec2ToFin_ones, weightedSum_vec2ToFin_ones]
    simpa using M.sumAffine.eval_succ t
  eval_wrap := by
    intro x y
    rw [weightedSum_vec2ToFin_ones, weightedSum_vec2ToFin_ones, weightedSum_vec2ToFin_ones]
    simpa using M.sumAffine.eval_wrap x y
  eval_recur := by
    intro b s n
    rw [weightedSum_vec2ToFin_ones, weightedSum_vec2ToFin_ones, weightedSum_vec2ToFin_ones,
      weightedSum_vec2ToFin_ones]
    simpa using M.sumAffine.eval_recur b s n
  h_weight_support := ⟨0, by simp⟩
  h_wrap_left_pos := M.h_wrap_left_pos
  h_wrap_right_pos := M.h_wrap_right_pos

/-- Re-derive the balanced mixed barrier from the functional theorem. -/
theorem no_matrixMix2_orients_dup_step_of_sum_pump_via_functional
    {S : StepDuplicatingSchema}
    (M : MatrixMix2Measure S)
    (hunbounded : HasUnboundedRangeSum M) :
    ¬ (∀ (b s n : S.T),
      PairLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  have hvec :
      ¬ (∀ (b s n : S.T),
        VecLt ((M.toFunctional).eval (S.wrap s (S.recur b s n)))
          ((M.toFunctional).eval (S.recur b s (S.succ n)))) := by
    apply no_matrixFunctional_orients_dup_step_of_componentwise_pump (M := M.toFunctional)
    intro k
    rcases hunbounded k with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    simpa [MatrixMix2Measure.toFunctional, weightedSum_vec2ToFin_ones] using ht
  apply hvec
  intro b s n i
  cases i using Fin.cases with
  | zero =>
      exact (h b s n).1
  | succ i =>
      fin_cases i
      exact (h b s n).2

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating

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
