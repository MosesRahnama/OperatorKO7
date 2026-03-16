import OperatorKO7.Meta.MatrixBarrier2

/-!
# Mixed Coordinate Dimension-2 Matrix Barrier

This module extends the tracked-coordinate matrix barriers to a genuinely mixed
two-dimensional class. Each constructor may mix both coordinates through a full
`2×2` linear map. The barrier is proved for a balanced regime: the two column
sums of each map agree, so the aggregate sum of the two coordinates becomes a
scalar affine measure.

This is still narrower than arbitrary mixed matrix interpretations, but it is no
longer a single-coordinate projection theorem. Off-diagonal coefficients may be
nonzero throughout.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-- Coordinate sum on `Nat × Nat`. -/
@[simp] def vecSum (v : Vec2) : Nat := v.1 + v.2

/-- A `2×2` linear map over `Nat`. -/
structure Lin2 where
  a11 : Nat
  a12 : Nat
  a21 : Nat
  a22 : Nat

namespace Lin2

/-- Apply a `2×2` linear map to a vector. -/
@[simp] def act (A : Lin2) (v : Vec2) : Vec2 :=
  (A.a11 * v.1 + A.a12 * v.2, A.a21 * v.1 + A.a22 * v.2)

/-- Balanced column sums, making the aggregate coordinate sum scalar-affine. -/
def Balanced (A : Lin2) : Prop :=
  A.a11 + A.a21 = A.a12 + A.a22

/-- Common column sum in the balanced case. -/
@[simp] def sumCoeff (A : Lin2) : Nat := A.a11 + A.a21

/-- The aggregate coordinate sum of a balanced map factors through one scalar coefficient. -/
lemma vecSum_act_eq (A : Lin2) (hbal : A.Balanced) (v : Vec2) :
    vecSum (A.act v) = A.sumCoeff * vecSum v := by
  dsimp [vecSum, act, sumCoeff, Balanced] at hbal ⊢
  calc
    A.a11 * v.1 + A.a12 * v.2 + (A.a21 * v.1 + A.a22 * v.2)
        = (A.a11 + A.a21) * v.1 + (A.a12 + A.a22) * v.2 := by ring
    _ = (A.a11 + A.a21) * v.1 + (A.a11 + A.a21) * v.2 := by rw [← hbal]
    _ = (A.a11 + A.a21) * (v.1 + v.2) := by ring

end Lin2

/-- A genuinely mixed dimension-2 affine measure with balanced `2×2` coefficient maps. -/
structure MatrixMix2Measure (S : StepDuplicatingSchema) where
  eval : S.T → Vec2
  c_base : Vec2
  succ_bias : Vec2
  succ_mat : Lin2
  wrap_bias : Vec2
  wrap_left : Lin2
  wrap_right : Lin2
  recur_bias : Vec2
  recur_base : Lin2
  recur_step : Lin2
  recur_counter : Lin2
  eval_base : eval S.base = c_base
  eval_succ :
    ∀ t, eval (S.succ t) = (succ_bias.1 + (succ_mat.act (eval t)).1,
      succ_bias.2 + (succ_mat.act (eval t)).2)
  eval_wrap :
    ∀ x y, eval (S.wrap x y) = (wrap_bias.1 + (wrap_left.act (eval x)).1 + (wrap_right.act (eval y)).1,
      wrap_bias.2 + (wrap_left.act (eval x)).2 + (wrap_right.act (eval y)).2)
  eval_recur :
    ∀ b s n, eval (S.recur b s n) =
      (recur_bias.1 + (recur_base.act (eval b)).1 + (recur_step.act (eval s)).1 + (recur_counter.act (eval n)).1,
       recur_bias.2 + (recur_base.act (eval b)).2 + (recur_step.act (eval s)).2 + (recur_counter.act (eval n)).2)
  h_succ_balanced : succ_mat.Balanced
  h_wrap_left_balanced : wrap_left.Balanced
  h_wrap_right_balanced : wrap_right.Balanced
  h_recur_base_balanced : recur_base.Balanced
  h_recur_step_balanced : recur_step.Balanced
  h_recur_counter_balanced : recur_counter.Balanced
  h_wrap_left_pos : 1 ≤ wrap_left.sumCoeff
  h_wrap_right_pos : 1 ≤ wrap_right.sumCoeff

/-- Aggregate-sum projection of the mixed matrix measure to the scalar affine barrier. -/
def MatrixMix2Measure.sumAffine {S : StepDuplicatingSchema}
    (M : MatrixMix2Measure S) : AffineMeasure S where
  eval := fun t => vecSum (M.eval t)
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
    simpa [vecSum] using congrArg vecSum M.eval_base
  eval_succ := by
    intro t
    have hact := Lin2.vecSum_act_eq M.succ_mat M.h_succ_balanced (M.eval t)
    rw [M.eval_succ]
    dsimp [vecSum] at hact ⊢
    omega
  eval_wrap := by
    intro x y
    have hleft := Lin2.vecSum_act_eq M.wrap_left M.h_wrap_left_balanced (M.eval x)
    have hright := Lin2.vecSum_act_eq M.wrap_right M.h_wrap_right_balanced (M.eval y)
    rw [M.eval_wrap]
    dsimp [vecSum] at hleft hright ⊢
    omega
  eval_recur := by
    intro b s n
    have hbase := Lin2.vecSum_act_eq M.recur_base M.h_recur_base_balanced (M.eval b)
    have hstep := Lin2.vecSum_act_eq M.recur_step M.h_recur_step_balanced (M.eval s)
    have hcnt := Lin2.vecSum_act_eq M.recur_counter M.h_recur_counter_balanced (M.eval n)
    rw [M.eval_recur]
    dsimp [vecSum] at hbase hstep hcnt ⊢
    omega
  h_wrap_left_pos := M.h_wrap_left_pos
  h_wrap_right_pos := M.h_wrap_right_pos

/-- Unbounded pump in the aggregate coordinate sum. -/
def HasUnboundedRangeSum {S : StepDuplicatingSchema} (M : MatrixMix2Measure S) : Prop :=
  ∀ k : Nat, ∃ t : S.T, k ≤ vecSum (M.eval t)

/-- Strict componentwise decrease forces strict decrease of the aggregate coordinate sum. -/
lemma vecSum_lt_of_pairLt {u v : Vec2} (h : PairLt u v) :
    vecSum u < vecSum v := by
  exact Nat.add_lt_add h.1 h.2

/-- Balanced mixed-coordinate componentwise orientation is impossible once the aggregate
coordinate sum has an unbounded pump. -/
theorem no_matrixMix2_orients_dup_step_of_sum_pump
    {S : StepDuplicatingSchema} (M : MatrixMix2Measure S)
    (hunbounded : HasUnboundedRangeSum M) :
    ¬ (∀ (b s n : S.T),
      PairLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  have hsum :
      ∀ (b s n : S.T),
        vecSum (M.eval (S.wrap s (S.recur b s n))) <
          vecSum (M.eval (S.recur b s (S.succ n))) := by
    intro b s n
    exact vecSum_lt_of_pairLt (h b s n)
  have hunbounded' : HasUnboundedRange M.sumAffine := by
    intro k
    rcases hunbounded k with ⟨t, ht⟩
    exact ⟨t, ht⟩
  exact
    no_affine_orients_dup_step_of_unbounded
      (S := S) M.sumAffine hunbounded' hsum

/-- The mixed sum barrier also lifts to global root orientation. -/
theorem no_global_orients_matrixMix2_of_sum_pump
    {Sys : StepDuplicatingSystem} (M : MatrixMix2Measure Sys.toStepDuplicatingSchema)
    (hunbounded : HasUnboundedRangeSum M) :
    ¬ GlobalOrients Sys M.eval PairLt := by
  intro h
  exact
    no_matrixMix2_orients_dup_step_of_sum_pump
      (S := Sys.toStepDuplicatingSchema) M hunbounded
      (fun b s n => h (Sys.dup_step b s n))

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating

namespace OperatorKO7.MatrixBarrierMix2

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

/-- KO7 specialization of the balanced mixed-coordinate dimension-2 barrier. -/
theorem no_global_step_orientation_matrixMix2_of_sum_pump
    (M : StepDuplicatingSchema.MatrixMix2Measure ko7Schema)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRangeSum M) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval StepDuplicatingSchema.PairLt := by
  exact
    StepDuplicatingSchema.no_global_orients_matrixMix2_of_sum_pump
      (Sys := ko7System) M hunbounded

end OperatorKO7.MatrixBarrierMix2
