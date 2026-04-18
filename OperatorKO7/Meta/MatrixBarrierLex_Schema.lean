import OperatorKO7.Meta.MatrixBarrier2_Schema

/-!
# Dimension-2 Lexicographic Affine Barrier

This module extends the tracked-component pair barrier from strict componentwise order
to a lexicographic order on `Nat × Nat`.  The theorem is still deliberately narrow:
the first component is the tracked affine component, and the proof shows that one can
force a strict increase in that primary component on the duplicating step.  Once the
primary component rises, lexicographic decrease is impossible regardless of the second
component.

This is a concrete extension of the current barrier frontier, not a general matrix
interpretation theory.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-- Strict lexicographic order on pairs, primary component first. -/
def PairLexLt (u v : Vec2) : Prop :=
  u.1 < v.1 ∨ (u.1 = v.1 ∧ u.2 < v.2)

/-- Any lexicographic decrease forces the first component to be non-increasing. -/
theorem fst_le_of_pairLexLt {u v : Vec2} (h : PairLexLt u v) : u.1 ≤ v.1 := by
  cases h with
  | inl hlt => exact Nat.le_of_lt hlt
  | inr heq => exact Nat.le_of_eq heq.1

/-- The tracked first component can be pumped high enough to force a *strict* first-component
increase on the duplicating step. This rules out lexicographic decrease immediately. -/
theorem no_matrix2_lex_orients_dup_step_of_unbounded_primary
    {S : StepDuplicatingSchema} (M : MatrixMeasure2 S)
    (hunbounded : HasUnboundedRange1 M) :
    ¬ (∀ (b s n : S.T),
      PairLexLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  let threshold := M.recur_counter1 * (M.succ_bias1 + M.succ_scale1 * M.c_base1)
  rcases hunbounded (threshold + 1) with ⟨s, hs⟩
  let Sval := (M.eval s).1
  let A := M.recur_const1 + M.recur_base1 * M.c_base1 + M.recur_step1 * Sval
  let B := M.recur_counter1 * M.c_base1
  let T := M.recur_counter1 * (M.succ_bias1 + M.succ_scale1 * M.c_base1)
  have hspec := h S.base s S.base
  have hle_spec :
      (M.eval (S.wrap s (S.recur S.base s S.base))).1 ≤
        (M.eval (S.recur S.base s (S.succ S.base))).1 := by
    exact fst_le_of_pairLexLt hspec
  have hle_spec' :
      M.wrap_const1 + M.wrap_left1 * Sval + M.wrap_right1 * (A + B) ≤ A + T := by
    simpa [Sval, A, B, T, M.eval_base, M.eval_succ1, M.eval_wrap1, M.eval_recur1,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.mul_add] using hle_spec
  have hsT1 : T + 1 ≤ Sval := by
    simpa [threshold, T, Sval] using hs
  have hS : Sval ≤ M.wrap_left1 * Sval := by
    calc
      Sval = 1 * Sval := by simp
      _ ≤ M.wrap_left1 * Sval := by
        exact Nat.mul_le_mul_right Sval M.h_wrap_left1_pos
  have hAB : A + B ≤ M.wrap_right1 * (A + B) := by
    calc
      A + B = 1 * (A + B) := by simp
      _ ≤ M.wrap_right1 * (A + B) := by
        exact Nat.mul_le_mul_right (A + B) M.h_wrap_right1_pos
  have h_rhs_to_aS1 : A + (T + 1) ≤ A + Sval := Nat.add_le_add_left hsT1 A
  have h_aS_to_aWS : A + Sval ≤ A + M.wrap_left1 * Sval := Nat.add_le_add_left hS A
  have h_aWS_to_sum : A + M.wrap_left1 * Sval ≤ A + M.wrap_left1 * Sval + B := by
    exact Nat.le_add_right _ _
  have h_sum_to_wsum :
      A + M.wrap_left1 * Sval + B ≤ M.wrap_left1 * Sval + M.wrap_right1 * (A + B) := by
    have hAB' :
        M.wrap_left1 * Sval + (A + B) ≤
          M.wrap_left1 * Sval + M.wrap_right1 * (A + B) :=
      Nat.add_le_add_left hAB (M.wrap_left1 * Sval)
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hAB'
  have h_with_const :
      M.wrap_left1 * Sval + M.wrap_right1 * (A + B) ≤
        M.wrap_const1 + M.wrap_left1 * Sval + M.wrap_right1 * (A + B) := by
    calc
      M.wrap_left1 * Sval + M.wrap_right1 * (A + B)
          ≤ M.wrap_const1 + (M.wrap_left1 * Sval + M.wrap_right1 * (A + B)) := by
            exact Nat.le_add_left _ _
      _ = M.wrap_const1 + M.wrap_left1 * Sval + M.wrap_right1 * (A + B) := by
        simp [Nat.add_assoc]
  have hgt :
      A + T + 1 ≤ M.wrap_const1 + M.wrap_left1 * Sval + M.wrap_right1 * (A + B) := by
    have htmp :
        A + (T + 1) ≤ M.wrap_const1 + M.wrap_left1 * Sval + M.wrap_right1 * (A + B) := by
      exact le_trans h_rhs_to_aS1 <|
        le_trans h_aS_to_aWS <|
        le_trans h_aWS_to_sum <|
        le_trans h_sum_to_wsum h_with_const
    simpa [Nat.add_assoc] using htmp
  omega

/-- Successor-pump corollary for lexicographic primary-component tracking. -/
theorem no_matrix2_lex_orients_dup_step_of_succ_pump
    {S : StepDuplicatingSchema} (M : MatrixMeasure2 S)
    (h_succ_bias : 1 ≤ M.succ_bias1) (h_succ_scale : 1 ≤ M.succ_scale1) :
    ¬ (∀ (b s n : S.T),
      PairLexLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  apply no_matrix2_lex_orients_dup_step_of_unbounded_primary (M := M)
  intro k
  refine ⟨succIter S k, ?_⟩
  simpa [MatrixMeasure2.fstAffine] using
    (eval_succIter_ge M.fstAffine h_succ_bias h_succ_scale k)

/-- Wrap-pump corollary for lexicographic primary-component tracking. -/
theorem no_matrix2_lex_orients_dup_step_of_wrap_pump
    {S : StepDuplicatingSchema} (M : MatrixMeasure2 S)
    (h_wrap_bias : 1 ≤ M.wrap_const1 + M.wrap_right1 * M.c_base1) :
    ¬ (∀ (b s n : S.T),
      PairLexLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  apply no_matrix2_lex_orients_dup_step_of_unbounded_primary (M := M)
  intro k
  refine ⟨wrapIter S k, ?_⟩
  simpa [MatrixMeasure2.fstAffine] using
    (eval_wrapIter_ge_affine M.fstAffine h_wrap_bias k)

/-- A lexicographically globally oriented system containing the duplicating step
would orient that step as well. -/
theorem no_global_orients_matrix2_lex_of_componentwise_pump
    {Sys : StepDuplicatingSystem} (M : MatrixMeasure2 Sys.toStepDuplicatingSchema)
    (hunbounded : HasUnboundedRange1 M) :
    ¬ GlobalOrients Sys M.eval PairLexLt := by
  intro h
  exact
    no_matrix2_lex_orients_dup_step_of_unbounded_primary
      (S := Sys.toStepDuplicatingSchema) M hunbounded
      (fun b s n => h (Sys.dup_step b s n))

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
