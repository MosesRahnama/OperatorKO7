import OperatorKO7.Meta.CompositionalMeasure_Impossibility

/-!
# Schema-Level Max Barrier

This module promotes the KO7-specific max-depth obstruction to a schema-level
max-plus direct family. The class is intentionally narrow:

- `succ` adds a fixed unary bump,
- `wrap` is a max of two visible branches plus a fixed outer bump,
- `recur` is a max of the base, step, and counter branches plus a fixed outer bump.

The contradiction uses the same pump idea as the additive barriers, but with a
different aggregation regime. Once the pumped step branch dominates the frozen
base and counter branches, the wrapper carries that same branch visibly, so the
target cannot be strictly smaller than the source.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-- A narrow max-plus constructor-local family. -/
structure MaxMeasure (S : StepDuplicatingSchema) where
  eval : S.T → Nat
  c_base : Nat
  succ_const : Nat
  wrap_const : Nat
  wrap_left : Nat
  wrap_right : Nat
  recur_const : Nat
  recur_base : Nat
  recur_step : Nat
  recur_counter : Nat
  eval_base : eval S.base = c_base
  eval_succ : ∀ t, eval (S.succ t) = succ_const + eval t
  eval_wrap :
    ∀ x y,
      eval (S.wrap x y) =
        wrap_const + max (wrap_left + eval x) (wrap_right + eval y)
  eval_recur :
    ∀ b s n,
      eval (S.recur b s n) =
        recur_const + max (recur_base + eval b)
          (max (recur_step + eval s) (recur_counter + eval n))
  h_wrap_right_pos : 1 ≤ wrap_right

/-- Unbounded range hypothesis for the max barrier. -/
def HasUnboundedRangeMax {S : StepDuplicatingSchema} (M : MaxMeasure S) : Prop :=
  ∀ k : Nat, ∃ t : S.T, k ≤ M.eval t

/-- Positive successor drift pumps the max family. -/
lemma eval_succIter_ge_max {S : StepDuplicatingSchema} (M : MaxMeasure S)
    (h_succ_const : 1 ≤ M.succ_const) (k : Nat) :
    k ≤ M.eval (succIter S k) := by
  induction k with
  | zero =>
      rw [succIter, M.eval_base]
      omega
  | succ k ih =>
      simp [succIter, M.eval_succ]
      nlinarith

/-- A positive wrap/base drift also pumps the max family. -/
lemma eval_wrapIter_ge_max {S : StepDuplicatingSchema} (M : MaxMeasure S)
    (h_wrap_drift : 1 ≤ M.wrap_const + M.wrap_left) (k : Nat) :
    k ≤ M.eval (wrapIter S k) := by
  induction k with
  | zero =>
      rw [wrapIter, M.eval_base]
      omega
  | succ k ih =>
      simp [wrapIter, M.eval_wrap, M.eval_base]
      have hmax :
          M.wrap_left + M.eval (wrapIter S k) ≤
            max (M.wrap_left + M.eval (wrapIter S k)) (M.wrap_right + M.c_base) := by
        exact le_max_left _ _
      have hgrow :
          1 + M.eval (wrapIter S k) ≤
            M.wrap_const +
              max (M.wrap_left + M.eval (wrapIter S k)) (M.wrap_right + M.c_base) := by
        calc
          1 + M.eval (wrapIter S k)
              ≤ (M.wrap_const + M.wrap_left) + M.eval (wrapIter S k) := by
                nlinarith
          _ = M.wrap_const + (M.wrap_left + M.eval (wrapIter S k)) := by omega
          _ ≤ M.wrap_const +
                max (M.wrap_left + M.eval (wrapIter S k)) (M.wrap_right + M.c_base) := by
                exact Nat.add_le_add_left hmax _
      omega

/-- Schema-level max barrier under an unbounded pump. -/
theorem no_max_orients_dup_step_of_unbounded
    {S : StepDuplicatingSchema} (M : MaxMeasure S)
    (hunbounded : HasUnboundedRangeMax M) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  intro h
  let succBase := M.succ_const + M.c_base
  let threshold := max (M.recur_base + M.c_base) (M.recur_counter + succBase)
  rcases hunbounded threshold with ⟨s, hs⟩
  let Sval := M.eval s
  have hs_base : M.recur_base + M.c_base ≤ M.recur_step + Sval := by
    have h0 : M.recur_base + M.c_base ≤ threshold := le_max_left _ _
    have h1 : threshold ≤ Sval := by simpa [threshold, Sval] using hs
    exact le_trans h0 <| le_trans h1 (Nat.le_add_left _ _)
  have hs_ctr_src : M.recur_counter + succBase ≤ M.recur_step + Sval := by
    have h0 : M.recur_counter + succBase ≤ threshold := le_max_right _ _
    have h1 : threshold ≤ Sval := by simpa [threshold, Sval] using hs
    exact le_trans h0 <| le_trans h1 (Nat.le_add_left _ _)
  have hs_ctr_tgt : M.recur_counter + M.c_base ≤ M.recur_step + Sval := by
    calc
      M.recur_counter + M.c_base ≤ M.recur_counter + succBase := by
        simp [succBase]
      _ ≤ M.recur_step + Sval := hs_ctr_src
  have hsrc_eq :
      M.eval (S.recur S.base s (S.succ S.base)) = M.recur_const + (M.recur_step + Sval) := by
    rw [M.eval_recur, M.eval_succ, M.eval_base]
    have hs_base' : M.c_base + M.recur_base ≤ M.recur_step + Sval := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hs_base
    have hs_ctr_src' : M.c_base + (M.succ_const + M.recur_counter) ≤ M.recur_step + Sval := by
      simpa [succBase, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hs_ctr_src
    have hmax :
        max (M.c_base + M.recur_base)
            (max (M.recur_step + Sval) (M.c_base + (M.succ_const + M.recur_counter))) =
          M.recur_step + Sval := by
      have hinner :
          max (M.recur_step + Sval) (M.c_base + (M.succ_const + M.recur_counter)) =
            M.recur_step + Sval :=
        max_eq_left hs_ctr_src'
      rw [hinner]
      exact max_eq_right hs_base'
    simp [Sval, Nat.add_left_comm, Nat.add_comm, hmax]
  have hinner_eq :
      M.eval (S.recur S.base s S.base) = M.recur_const + (M.recur_step + Sval) := by
    rw [M.eval_recur, M.eval_base]
    have hs_base' : M.c_base + M.recur_base ≤ M.recur_step + Sval := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hs_base
    have hs_ctr_tgt' : M.c_base + M.recur_counter ≤ M.recur_step + Sval := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hs_ctr_tgt
    have hmax :
        max (M.c_base + M.recur_base)
            (max (M.recur_step + Sval) (M.c_base + M.recur_counter)) =
          M.recur_step + Sval := by
      have hinner :
          max (M.recur_step + Sval) (M.c_base + M.recur_counter) =
            M.recur_step + Sval :=
        max_eq_left hs_ctr_tgt'
      rw [hinner]
      exact max_eq_right hs_base'
    simp [Sval, Nat.add_comm, hmax]
  have hspec := h S.base s S.base
  rw [hsrc_eq, M.eval_wrap, hinner_eq] at hspec
  have htarget_ge :
      M.recur_const + (M.recur_step + Sval) + 1 ≤
        M.wrap_const +
          max (M.wrap_left + Sval) (M.wrap_right + (M.recur_const + (M.recur_step + Sval))) := by
    have hright :
        M.recur_const + (M.recur_step + Sval) + 1 ≤
          M.wrap_right + (M.recur_const + (M.recur_step + Sval)) := by
      nlinarith [M.h_wrap_right_pos]
    have hmax :
        M.wrap_right + (M.recur_const + (M.recur_step + Sval)) ≤
          max (M.wrap_left + Sval) (M.wrap_right + (M.recur_const + (M.recur_step + Sval))) := by
      exact le_max_right _ _
    exact le_trans hright <| le_trans hmax (Nat.le_add_left _ _)
  have hge :
      M.recur_const + (M.recur_step + Sval) <
        M.wrap_const +
          max (M.wrap_left + Sval) (M.wrap_right + (M.recur_const + (M.recur_step + Sval))) := by
    omega
  exact Nat.not_lt_of_ge (Nat.le_of_lt hge) hspec

/-- Successor-pump specialization of the max barrier. -/
theorem no_max_orients_dup_step_of_succ_pump
    {S : StepDuplicatingSchema} (M : MaxMeasure S)
    (h_succ_const : 1 ≤ M.succ_const) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  apply no_max_orients_dup_step_of_unbounded (M := M)
  intro k
  refine ⟨succIter S k, ?_⟩
  simpa using eval_succIter_ge_max (M := M) h_succ_const k

/-- Wrap-pump specialization of the max barrier. -/
theorem no_max_orients_dup_step_of_wrap_pump
    {S : StepDuplicatingSchema} (M : MaxMeasure S)
    (h_wrap_drift : 1 ≤ M.wrap_const + M.wrap_left) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  apply no_max_orients_dup_step_of_unbounded (M := M)
  intro k
  refine ⟨wrapIter S k, ?_⟩
  simpa using eval_wrapIter_ge_max (M := M) h_wrap_drift k

/-- The max barrier lifts to global root orientation. -/
theorem no_global_orients_max_of_unbounded
    {Sys : StepDuplicatingSystem} (M : MaxMeasure Sys.toStepDuplicatingSchema)
    (hunbounded : HasUnboundedRangeMax M) :
    ¬ GlobalOrients Sys M.eval (· < ·) := by
  intro h
  exact
    no_max_orients_dup_step_of_unbounded
      (S := Sys.toStepDuplicatingSchema) M hunbounded
      (fun b s n => h (Sys.dup_step b s n))

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating

namespace OperatorKO7.MaxBarrier

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

/-- KO7 specialization of the schema-level max barrier. -/
theorem no_global_step_orientation_max_of_unbounded
    (M : StepDuplicatingSchema.MaxMeasure ko7Schema)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRangeMax M) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval (· < ·) := by
  exact
    StepDuplicatingSchema.no_global_orients_max_of_unbounded
      (Sys := ko7System) M hunbounded

/-- KO7 successor-pump specialization of the schema-level max barrier. -/
theorem no_global_step_orientation_max_of_succ_pump
    (M : StepDuplicatingSchema.MaxMeasure ko7Schema)
    (h_succ_const : 1 ≤ M.succ_const) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval (· < ·) := by
  apply no_global_step_orientation_max_of_unbounded (M := M)
  intro k
  refine ⟨StepDuplicatingSchema.succIter ko7Schema k, ?_⟩
  simpa using StepDuplicatingSchema.eval_succIter_ge_max (M := M) h_succ_const k

/-- KO7 wrap-pump specialization of the schema-level max barrier. -/
theorem no_global_step_orientation_max_of_wrap_pump
    (M : StepDuplicatingSchema.MaxMeasure ko7Schema)
    (h_wrap_drift : 1 ≤ M.wrap_const + M.wrap_left) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval (· < ·) := by
  apply no_global_step_orientation_max_of_unbounded (M := M)
  intro k
  refine ⟨StepDuplicatingSchema.wrapIter ko7Schema k, ?_⟩
  simpa using StepDuplicatingSchema.eval_wrapIter_ge_max (M := M) h_wrap_drift k

end OperatorKO7.MaxBarrier
