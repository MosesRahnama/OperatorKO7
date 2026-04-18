import OperatorKO7.Meta.StepDuplicatingSchema

/-!
# Finite-Dimension Lexicographic Barrier with Tracked Primary Coordinate

This module generalizes the tracked-primary lexicographic barrier from dimension `2`
to arbitrary fixed finite dimension.

The proof remains intentionally structural rather than fully matrix-theoretic:
only the primary coordinate is assumed to satisfy the affine barrier interface.
All remaining coordinates may behave arbitrarily. Any lexicographic decrease still
forces the primary coordinate to be non-increasing, so a pumped strict increase in that
coordinate blocks lexicographic orientation immediately.

This yields a genuinely broader direct-family impossibility theorem than the previous
dimension-2 lex result: any finite tracked-primary lexicographic direct order falls on the
barrier side once its primary coordinate admits the standard successor- or wrapper-pump.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-- The distinguished primary coordinate for a lexicographic vector family. -/
@[simp] def primaryIdx (d : Nat) : Fin (d + 1) := ⟨0, Nat.succ_pos d⟩

/-- Strict lexicographic order on `Fin (d+1) → Nat`, with the natural `Fin` ordering. -/
def VecLexLt {d : Nat} (u v : Fin (d + 1) → Nat) : Prop :=
  ∃ i : Fin (d + 1),
    (∀ j : Fin (d + 1), j.val < i.val → u j = v j) ∧ u i < v i

/-- Any lexicographic decrease forces the primary coordinate to be non-increasing. -/
theorem primary_le_of_vecLexLt {d : Nat} {u v : Fin (d + 1) → Nat}
    (h : VecLexLt u v) :
    u (primaryIdx d) ≤ v (primaryIdx d) := by
  rcases h with ⟨i, hprefix, hlt⟩
  by_cases hi : i = primaryIdx d
  · subst hi
    exact Nat.le_of_lt hlt
  · have hpos : 0 < i.val := by
      apply Nat.pos_of_ne_zero
      intro hz
      apply hi
      apply Fin.ext
      simpa [primaryIdx] using hz
    have heq := hprefix (primaryIdx d) hpos
    exact Nat.le_of_eq heq

/-- A finite-dimensional lexicographic direct measure with one tracked affine primary
coordinate. All other coordinates are intentionally left unconstrained. -/
structure MatrixLexMeasureD (S : StepDuplicatingSchema) (d : Nat) where
  eval : S.T → Fin (d + 1) → Nat
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
  eval_base : eval S.base (primaryIdx d) = c_base
  eval_succ :
    ∀ t, eval (S.succ t) (primaryIdx d) = succ_bias + succ_scale * eval t (primaryIdx d)
  eval_wrap :
    ∀ x y,
      eval (S.wrap x y) (primaryIdx d) =
        wrap_const + wrap_left * eval x (primaryIdx d) + wrap_right * eval y (primaryIdx d)
  eval_recur :
    ∀ b s n,
      eval (S.recur b s n) (primaryIdx d) =
        recur_const + recur_base * eval b (primaryIdx d) +
          recur_step * eval s (primaryIdx d) + recur_counter * eval n (primaryIdx d)
  h_wrap_left_pos : 1 ≤ wrap_left
  h_wrap_right_pos : 1 ≤ wrap_right

/-- Project the primary coordinate to the scalar affine barrier infrastructure. -/
def MatrixLexMeasureD.primaryAffine
    {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixLexMeasureD S d) : AffineMeasure S where
  eval := fun t => M.eval t (primaryIdx d)
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

/-- Unbounded pump in the tracked primary coordinate. -/
def HasUnboundedPrimaryRange
    {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixLexMeasureD S d) : Prop :=
  ∀ k : Nat, ∃ t : S.T, k ≤ M.eval t (primaryIdx d)

/-- A pumped strict increase in the primary coordinate blocks finite-dimensional
lexicographic orientation immediately. -/
theorem no_matrixLexD_orients_dup_step_of_unbounded_primary
    {S : StepDuplicatingSchema} {d : Nat} (M : MatrixLexMeasureD S d)
    (hunbounded : HasUnboundedPrimaryRange M) :
    ¬ (∀ (b s n : S.T),
      VecLexLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  let threshold := M.recur_counter * (M.succ_bias + M.succ_scale * M.c_base)
  rcases hunbounded (threshold + 1) with ⟨s, hs⟩
  let Sval := M.eval s (primaryIdx d)
  let A := M.recur_const + M.recur_base * M.c_base + M.recur_step * Sval
  let B := M.recur_counter * M.c_base
  let T := M.recur_counter * (M.succ_bias + M.succ_scale * M.c_base)
  have hspec := h S.base s S.base
  have hle_spec :
      M.eval (S.wrap s (S.recur S.base s S.base)) (primaryIdx d) ≤
        M.eval (S.recur S.base s (S.succ S.base)) (primaryIdx d) := by
    exact primary_le_of_vecLexLt hspec
  have hle_spec' :
      M.wrap_const + M.wrap_left * Sval + M.wrap_right * (A + B) ≤ A + T := by
    rw [M.eval_wrap, M.eval_recur, M.eval_recur, M.eval_base, M.eval_succ, M.eval_base] at hle_spec
    simpa [Sval, A, B, T, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.mul_add] using hle_spec
  have hsT1 : T + 1 ≤ Sval := by
    simpa [threshold, T, Sval] using hs
  have hS : Sval ≤ M.wrap_left * Sval := by
    calc
      Sval = 1 * Sval := by simp
      _ ≤ M.wrap_left * Sval := by exact Nat.mul_le_mul_right Sval M.h_wrap_left_pos
  have hAB : A + B ≤ M.wrap_right * (A + B) := by
    calc
      A + B = 1 * (A + B) := by simp
      _ ≤ M.wrap_right * (A + B) := by
        exact Nat.mul_le_mul_right (A + B) M.h_wrap_right_pos
  have h_rhs_to_aS1 : A + (T + 1) ≤ A + Sval := Nat.add_le_add_left hsT1 A
  have h_aS_to_aWS : A + Sval ≤ A + M.wrap_left * Sval := Nat.add_le_add_left hS A
  have h_aWS_to_sum : A + M.wrap_left * Sval ≤ A + M.wrap_left * Sval + B := by
    exact Nat.le_add_right _ _
  have h_sum_to_wsum :
      A + M.wrap_left * Sval + B ≤ M.wrap_left * Sval + M.wrap_right * (A + B) := by
    have hAB' :
        M.wrap_left * Sval + (A + B) ≤
          M.wrap_left * Sval + M.wrap_right * (A + B) :=
      Nat.add_le_add_left hAB (M.wrap_left * Sval)
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hAB'
  have h_with_const :
      M.wrap_left * Sval + M.wrap_right * (A + B) ≤
        M.wrap_const + M.wrap_left * Sval + M.wrap_right * (A + B) := by
    calc
      M.wrap_left * Sval + M.wrap_right * (A + B)
          ≤ M.wrap_const + (M.wrap_left * Sval + M.wrap_right * (A + B)) := by
            exact Nat.le_add_left _ _
      _ = M.wrap_const + M.wrap_left * Sval + M.wrap_right * (A + B) := by
        simp [Nat.add_assoc]
  have hgt :
      A + T + 1 ≤ M.wrap_const + M.wrap_left * Sval + M.wrap_right * (A + B) := by
    have htmp :
        A + (T + 1) ≤ M.wrap_const + M.wrap_left * Sval + M.wrap_right * (A + B) := by
      exact le_trans h_rhs_to_aS1 <|
        le_trans h_aS_to_aWS <|
        le_trans h_aWS_to_sum <|
        le_trans h_sum_to_wsum h_with_const
    simpa [Nat.add_assoc] using htmp
  omega

/-- Successor-pump corollary for finite lexicographic families. -/
theorem no_matrixLexD_orients_dup_step_of_succ_pump
    {S : StepDuplicatingSchema} {d : Nat} (M : MatrixLexMeasureD S d)
    (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale) :
    ¬ (∀ (b s n : S.T),
      VecLexLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  apply no_matrixLexD_orients_dup_step_of_unbounded_primary (M := M)
  intro k
  refine ⟨succIter S k, ?_⟩
  simpa [MatrixLexMeasureD.primaryAffine, primaryIdx] using
    (eval_succIter_ge M.primaryAffine h_succ_bias h_succ_scale k)

/-- Wrap-pump corollary for finite lexicographic families. -/
theorem no_matrixLexD_orients_dup_step_of_wrap_pump
    {S : StepDuplicatingSchema} {d : Nat} (M : MatrixLexMeasureD S d)
    (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base) :
    ¬ (∀ (b s n : S.T),
      VecLexLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  apply no_matrixLexD_orients_dup_step_of_unbounded_primary (M := M)
  intro k
  refine ⟨wrapIter S k, ?_⟩
  simpa [MatrixLexMeasureD.primaryAffine, primaryIdx] using
    (eval_wrapIter_ge_affine M.primaryAffine h_wrap_bias k)

/-- A strengthened finite lexicographic family with an internal primary pump. -/
structure MatrixLexMeasureDWithPrimaryPump (S : StepDuplicatingSchema) (d : Nat)
    extends MatrixLexMeasureD S d where
  has_primary_pump :
    (1 ≤ succ_bias ∧ 1 ≤ succ_scale) ∨ 1 ≤ wrap_const + wrap_right * c_base

/-- Unconditional barrier for the strengthened finite lexicographic subclass. -/
theorem no_matrixLexD_with_primary_pump_orients_dup_step
    {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixLexMeasureDWithPrimaryPump S d) :
    ¬ (∀ (b s n : S.T),
      VecLexLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  rcases M.has_primary_pump with hsucc | hwrap
  · exact no_matrixLexD_orients_dup_step_of_succ_pump (M := M.toMatrixLexMeasureD) hsucc.1 hsucc.2
  · exact no_matrixLexD_orients_dup_step_of_wrap_pump (M := M.toMatrixLexMeasureD) hwrap

/-- Global root orientation would orient the duplicating step as well. -/
theorem no_global_orients_matrixLexD_of_unbounded_primary
    {Sys : StepDuplicatingSystem} {d : Nat}
    (M : MatrixLexMeasureD Sys.toStepDuplicatingSchema d)
    (hunbounded : HasUnboundedPrimaryRange M) :
    ¬ GlobalOrients Sys M.eval VecLexLt := by
  intro h
  exact
    no_matrixLexD_orients_dup_step_of_unbounded_primary
      (S := Sys.toStepDuplicatingSchema) M hunbounded
      (fun b s n => h (Sys.dup_step b s n))

/-- The strengthened pumped finite lexicographic subclass also fails globally. -/
theorem no_global_orients_matrixLexD_with_primary_pump
    {Sys : StepDuplicatingSystem} {d : Nat}
    (M : MatrixLexMeasureDWithPrimaryPump Sys.toStepDuplicatingSchema d) :
    ¬ GlobalOrients Sys M.eval VecLexLt := by
  intro h
  exact
    no_matrixLexD_with_primary_pump_orients_dup_step
      (S := Sys.toStepDuplicatingSchema) M
      (fun b s n => h (Sys.dup_step b s n))

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
