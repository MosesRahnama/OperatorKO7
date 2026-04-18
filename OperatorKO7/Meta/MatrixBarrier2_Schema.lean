import OperatorKO7.Meta.StepDuplicatingSchema

/-!
# Dimension-2 Componentwise Affine Barrier

This is a first low-dimensional extension of the scalar affine barrier.  The value space is
`Nat × Nat`, ordered componentwise.  Each component is an affine constructor-local measure on
the same term algebra.  The primary theorem tracks the first component: if that component already
cannot decrease on the duplicating step, then componentwise decrease is impossible as well.
A symmetric theorem then shows the same for the second component under the corresponding
positivity hypotheses.

This is deliberately a **tracked-component** result rather than a full arbitrary `2×2` matrix
theory.  It is the smallest honest step from the scalar affine barrier toward matrix-style
interpretations.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

abbrev Vec2 := Nat × Nat

/-- Strict componentwise order on pairs. -/
def PairLt (u v : Vec2) : Prop := u.1 < v.1 ∧ u.2 < v.2

/-- Dimension-2 componentwise affine measures: each component is a scalar affine
constructor-local measure on the same term algebra. -/
structure MatrixMeasure2 (S : StepDuplicatingSchema) where
  eval : S.T → Vec2
  c_base1 : Nat
  c_base2 : Nat
  succ_bias1 : Nat
  succ_scale1 : Nat
  succ_bias2 : Nat
  succ_scale2 : Nat
  wrap_const1 : Nat
  wrap_left1 : Nat
  wrap_right1 : Nat
  wrap_const2 : Nat
  wrap_left2 : Nat
  wrap_right2 : Nat
  recur_const1 : Nat
  recur_base1 : Nat
  recur_step1 : Nat
  recur_counter1 : Nat
  recur_const2 : Nat
  recur_base2 : Nat
  recur_step2 : Nat
  recur_counter2 : Nat
  eval_base : eval S.base = (c_base1, c_base2)
  eval_succ1 : ∀ t, (eval (S.succ t)).1 = succ_bias1 + succ_scale1 * (eval t).1
  eval_succ2 : ∀ t, (eval (S.succ t)).2 = succ_bias2 + succ_scale2 * (eval t).2
  eval_wrap1 :
    ∀ x y, (eval (S.wrap x y)).1 =
      wrap_const1 + wrap_left1 * (eval x).1 + wrap_right1 * (eval y).1
  eval_wrap2 :
    ∀ x y, (eval (S.wrap x y)).2 =
      wrap_const2 + wrap_left2 * (eval x).2 + wrap_right2 * (eval y).2
  eval_recur1 :
    ∀ b s n, (eval (S.recur b s n)).1 =
      recur_const1 + recur_base1 * (eval b).1 +
        recur_step1 * (eval s).1 + recur_counter1 * (eval n).1
  eval_recur2 :
    ∀ b s n, (eval (S.recur b s n)).2 =
      recur_const2 + recur_base2 * (eval b).2 +
        recur_step2 * (eval s).2 + recur_counter2 * (eval n).2
  h_wrap_left1_pos : 1 ≤ wrap_left1
  h_wrap_right1_pos : 1 ≤ wrap_right1

/-- Project the first component to the existing scalar affine barrier infrastructure. -/
def MatrixMeasure2.fstAffine {S : StepDuplicatingSchema}
    (M : MatrixMeasure2 S) : AffineMeasure S where
  eval := fun t => (M.eval t).1
  c_base := M.c_base1
  succ_bias := M.succ_bias1
  succ_scale := M.succ_scale1
  wrap_const := M.wrap_const1
  wrap_left := M.wrap_left1
  wrap_right := M.wrap_right1
  recur_const := M.recur_const1
  recur_base := M.recur_base1
  recur_step := M.recur_step1
  recur_counter := M.recur_counter1
  eval_base := by simpa using congrArg Prod.fst M.eval_base
  eval_succ := M.eval_succ1
  eval_wrap := M.eval_wrap1
  eval_recur := M.eval_recur1
  h_wrap_left_pos := M.h_wrap_left1_pos
  h_wrap_right_pos := M.h_wrap_right1_pos

/-- Project the second component to the scalar affine barrier infrastructure.
The wrapper-positivity assumptions are supplied as theorem hypotheses rather than
being baked into the structure. -/
def MatrixMeasure2.sndAffine {S : StepDuplicatingSchema}
    (M : MatrixMeasure2 S)
    (h_wl2 : 1 ≤ M.wrap_left2) (h_wr2 : 1 ≤ M.wrap_right2) : AffineMeasure S where
  eval := fun t => (M.eval t).2
  c_base := M.c_base2
  succ_bias := M.succ_bias2
  succ_scale := M.succ_scale2
  wrap_const := M.wrap_const2
  wrap_left := M.wrap_left2
  wrap_right := M.wrap_right2
  recur_const := M.recur_const2
  recur_base := M.recur_base2
  recur_step := M.recur_step2
  recur_counter := M.recur_counter2
  eval_base := by simpa using congrArg Prod.snd M.eval_base
  eval_succ := M.eval_succ2
  eval_wrap := M.eval_wrap2
  eval_recur := M.eval_recur2
  h_wrap_left_pos := h_wl2
  h_wrap_right_pos := h_wr2

/-- Unbounded pump in the tracked first component. -/
def HasUnboundedRange1 {S : StepDuplicatingSchema} (M : MatrixMeasure2 S) : Prop :=
  ∀ k : Nat, ∃ t : S.T, k ≤ (M.eval t).1

/-- Unbounded pump in the second component. -/
def HasUnboundedRange2 {S : StepDuplicatingSchema} (M : MatrixMeasure2 S) : Prop :=
  ∀ k : Nat, ∃ t : S.T, k ≤ (M.eval t).2

/-- First-component affine failure already rules out componentwise pair orientation. -/
theorem no_matrix2_orients_dup_step_of_componentwise_pump
    {S : StepDuplicatingSchema} (M : MatrixMeasure2 S)
    (hunbounded : HasUnboundedRange1 M) :
    ¬ (∀ (b s n : S.T),
      PairLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  have hfst :
      ∀ (b s n : S.T),
        (M.eval (S.wrap s (S.recur b s n))).1 <
          (M.eval (S.recur b s (S.succ n))).1 := by
    intro b s n
    exact (h b s n).1
  have hunbounded' : HasUnboundedRange M.fstAffine := by
    intro k
    rcases hunbounded k with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    simpa [MatrixMeasure2.fstAffine] using ht
  exact
    no_affine_orients_dup_step_of_unbounded
      (S := S) M.fstAffine hunbounded' hfst

/-- Second-component affine failure also rules out componentwise pair orientation. -/
theorem no_matrix2_orients_dup_step_of_componentwise_pump_snd
    {S : StepDuplicatingSchema} (M : MatrixMeasure2 S)
    (h_wl2 : 1 ≤ M.wrap_left2) (h_wr2 : 1 ≤ M.wrap_right2)
    (hunbounded : HasUnboundedRange2 M) :
    ¬ (∀ (b s n : S.T),
      PairLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  have hsnd :
      ∀ (b s n : S.T),
        (M.eval (S.wrap s (S.recur b s n))).2 <
          (M.eval (S.recur b s (S.succ n))).2 := by
    intro b s n
    exact (h b s n).2
  have hunbounded' : HasUnboundedRange (M.sndAffine h_wl2 h_wr2) := by
    intro k
    rcases hunbounded k with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    simpa [MatrixMeasure2.sndAffine] using ht
  exact
    no_affine_orients_dup_step_of_unbounded
      (S := S) (M.sndAffine h_wl2 h_wr2) hunbounded' hsnd

/-- Successor-pump corollary for the tracked first component. -/
theorem no_matrix2_orients_dup_step_of_succ_pump
    {S : StepDuplicatingSchema} (M : MatrixMeasure2 S)
    (h_succ_bias : 1 ≤ M.succ_bias1) (h_succ_scale : 1 ≤ M.succ_scale1) :
    ¬ (∀ (b s n : S.T),
      PairLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  have hfst :
      ∀ (b s n : S.T),
        (M.eval (S.wrap s (S.recur b s n))).1 <
          (M.eval (S.recur b s (S.succ n))).1 := by
    intro b s n
    exact (h b s n).1
  exact
    no_affine_orients_dup_step_of_succ_pump
      (S := S) M.fstAffine h_succ_bias h_succ_scale hfst

/-- Wrap-pump corollary for the tracked first component. -/
theorem no_matrix2_orients_dup_step_of_wrap_pump
    {S : StepDuplicatingSchema} (M : MatrixMeasure2 S)
    (h_wrap_bias : 1 ≤ M.wrap_const1 + M.wrap_right1 * M.c_base1) :
    ¬ (∀ (b s n : S.T),
      PairLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  have hfst :
      ∀ (b s n : S.T),
        (M.eval (S.wrap s (S.recur b s n))).1 <
          (M.eval (S.recur b s (S.succ n))).1 := by
    intro b s n
    exact (h b s n).1
  exact
    no_affine_orients_dup_step_of_wrap_pump
      (S := S) M.fstAffine h_wrap_bias hfst

/-- The tracked-component barrier also lifts to global root orientation. -/
theorem no_global_orients_matrix2_of_componentwise_pump
    {Sys : StepDuplicatingSystem} (M : MatrixMeasure2 Sys.toStepDuplicatingSchema)
    (hunbounded : HasUnboundedRange1 M) :
    ¬ GlobalOrients Sys M.eval PairLt := by
  intro h
  exact
    no_matrix2_orients_dup_step_of_componentwise_pump
      (S := Sys.toStepDuplicatingSchema) M hunbounded
      (fun b s n => h (Sys.dup_step b s n))

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
