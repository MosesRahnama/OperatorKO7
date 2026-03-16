import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Typed Barrier Survival

This module tests whether the direct-measure barrier survives a simply-typed
first-order presentation of the duplicating recursor. The answer is yes for a
small typed fragment in which the step sort still admits an unbounded closed
family:

- the additive barrier survives outright via a typed step-iterator;
- the affine barrier survives under an explicit typed step-pump hypothesis.

The purpose is to show that simple typing by itself is not the missing escape
mechanism. More restrictive typed regimes, where every closed family of step
arguments is bounded, remain outside the present result.
-/

namespace OperatorKO7.TypedBarrierSurvival

/-- Simple first-order sorts for a typed recursor fragment. -/
inductive Ty
  | res
  | step
  | cnt
deriving DecidableEq, Repr

/-- Terms of the simply-typed recursor fragment. -/
inductive Term : Ty → Type
  | base : Term .res
  | zero : Term .cnt
  | succ : Term .cnt → Term .cnt
  | stepZero : Term .step
  | stepSucc : Term .step → Term .step
  | wrap : Term .step → Term .res → Term .res
  | recur : Term .res → Term .step → Term .cnt → Term .res
deriving Repr

open Ty Term

/-- Typed step-sort iterator. -/
def stepIter : Nat → Term .step
  | 0 => stepZero
  | n + 1 => stepSucc (stepIter n)

/-- Additive constructor-local measures on the typed fragment. -/
structure AdditiveMeasure where
  evalRes : Term .res → Nat
  evalStep : Term .step → Nat
  evalCnt : Term .cnt → Nat
  w_base : Nat
  w_zero : Nat
  w_cnt_succ : Nat
  w_step_zero : Nat
  w_step_succ : Nat
  w_wrap : Nat
  w_recur : Nat
  eval_base : evalRes base = w_base
  eval_zero : evalCnt zero = w_zero
  eval_cnt_succ : ∀ n, evalCnt (succ n) = w_cnt_succ + evalCnt n
  eval_step_zero : evalStep stepZero = w_step_zero
  eval_step_succ : ∀ s, evalStep (stepSucc s) = w_step_succ + evalStep s
  eval_wrap : ∀ s t, evalRes (wrap s t) = w_wrap + evalStep s + evalRes t
  eval_recur : ∀ b s n, evalRes (recur b s n) = w_recur + evalRes b + evalStep s + evalCnt n
  h_wrap_pos : 1 ≤ w_wrap
  h_step_succ_pos : 1 ≤ w_step_succ

/-- The typed step iterator still yields an unbounded additive pump. -/
lemma eval_stepIter_ge (M : AdditiveMeasure) (k : Nat) :
    k ≤ M.evalStep (stepIter k) := by
  induction k with
  | zero =>
      simp [stepIter, M.eval_step_zero]
  | succ k ih =>
      rw [stepIter, M.eval_step_succ]
      have hk : k + 1 ≤ M.w_step_succ + M.evalStep (stepIter k) := by
        have hpos := M.h_step_succ_pos
        omega
      exact hk

/-- No additive typed direct measure can orient the typed duplicating step
uniformly. -/
theorem no_additive_orients_typed_recSucc (M : AdditiveMeasure) :
    ¬ (∀ (b : Term .res) (s : Term .step) (n : Term .cnt),
      M.evalRes (wrap s (recur b s n)) < M.evalRes (recur b s (succ n))) := by
  intro h
  let s := stepIter M.w_cnt_succ
  have hs : M.w_cnt_succ ≤ M.evalStep s := by
    simpa [s] using eval_stepIter_ge M M.w_cnt_succ
  have hspec := h base s zero
  have hsrc :
      M.evalRes (recur base s (succ zero)) =
        M.w_recur + M.w_base + M.evalStep s + (M.w_cnt_succ + M.w_zero) := by
    rw [M.eval_recur, M.eval_base, M.eval_cnt_succ, M.eval_zero]
  have htgt :
      M.evalRes (wrap s (recur base s zero)) =
        M.w_wrap + M.evalStep s + (M.w_recur + M.w_base + M.evalStep s + M.w_zero) := by
    rw [M.eval_wrap, M.eval_recur, M.eval_base, M.eval_zero]
  rw [htgt, hsrc] at hspec
  have hwrap := M.h_wrap_pos
  omega

/-- Affine constructor-local measures on the typed fragment. -/
structure AffineMeasure where
  evalRes : Term .res → Nat
  evalStep : Term .step → Nat
  evalCnt : Term .cnt → Nat
  c_base : Nat
  c_zero : Nat
  cnt_succ_bias : Nat
  cnt_succ_scale : Nat
  step_zero : Nat
  step_succ_bias : Nat
  step_succ_scale : Nat
  wrap_const : Nat
  wrap_left : Nat
  wrap_right : Nat
  recur_const : Nat
  recur_base : Nat
  recur_step : Nat
  recur_counter : Nat
  eval_base : evalRes base = c_base
  eval_zero : evalCnt zero = c_zero
  eval_cnt_succ :
    ∀ n, evalCnt (succ n) = cnt_succ_bias + cnt_succ_scale * evalCnt n
  eval_step_zero : evalStep stepZero = step_zero
  eval_step_succ :
    ∀ s, evalStep (stepSucc s) = step_succ_bias + step_succ_scale * evalStep s
  eval_wrap :
    ∀ s t, evalRes (wrap s t) =
      wrap_const + wrap_left * evalStep s + wrap_right * evalRes t
  eval_recur :
    ∀ b s n, evalRes (recur b s n) =
      recur_const + recur_base * evalRes b + recur_step * evalStep s + recur_counter * evalCnt n
  h_wrap_left_pos : 1 ≤ wrap_left
  h_wrap_right_pos : 1 ≤ wrap_right

/-- Explicit typed step-pump hypothesis: the step sort still contains arbitrarily
large closed terms. -/
def HasTypedStepPump (M : AffineMeasure) : Prop :=
  ∀ k : Nat, ∃ s : Term .step, k ≤ M.evalStep s

/-- Coarse typed affine bound needed to force failure on the duplicating step. -/
def typedAffineBound (M : AffineMeasure) : Nat :=
  M.recur_counter * (M.cnt_succ_bias + M.cnt_succ_scale * M.c_zero)

/-- In the typed affine fragment, a sufficiently large typed step argument forces
the target to be at least as large as the source. -/
lemma typed_affine_target_ge_source_of_bound (M : AffineMeasure)
    {s : Term .step}
    (hs : typedAffineBound M ≤ M.evalStep s) :
    M.evalRes (recur base s (succ zero)) ≤
      M.evalRes (wrap s (recur base s zero)) := by
  let A :=
    M.recur_const + M.recur_base * M.c_base + M.recur_step * M.evalStep s
  have hsrc :
      M.evalRes (recur base s (succ zero)) =
        A + M.recur_counter * (M.cnt_succ_bias + M.cnt_succ_scale * M.c_zero) := by
    rw [M.eval_recur, M.eval_base, M.eval_cnt_succ, M.eval_zero]
  have htgt :
      M.evalRes (wrap s (recur base s zero)) =
        M.wrap_const + M.wrap_left * M.evalStep s +
          M.wrap_right * (A + M.recur_counter * M.c_zero) := by
    rw [M.eval_wrap, M.eval_recur, M.eval_base, M.eval_zero]
  rw [hsrc, htgt]
  have hcnt :
      M.recur_counter * (M.cnt_succ_bias + M.cnt_succ_scale * M.c_zero) ≤
        M.evalStep s + M.recur_counter * M.c_zero := by
    exact Nat.le_trans hs (Nat.le_add_right _ _)
  have hleft :
      M.evalStep s ≤ M.wrap_left * M.evalStep s := by
    have hmul := Nat.mul_le_mul_left (M.evalStep s) M.h_wrap_left_pos
    simpa [Nat.mul_comm] using hmul
  have hright :
      A + M.recur_counter * M.c_zero ≤
        M.wrap_right * (A + M.recur_counter * M.c_zero) := by
    have hmul := Nat.mul_le_mul_left (A + M.recur_counter * M.c_zero) M.h_wrap_right_pos
    simpa [Nat.mul_comm] using hmul
  calc
    A + M.recur_counter * (M.cnt_succ_bias + M.cnt_succ_scale * M.c_zero)
        ≤ A + (M.evalStep s + M.recur_counter * M.c_zero) := by
          exact Nat.add_le_add_left hcnt A
    _ = M.evalStep s + (A + M.recur_counter * M.c_zero) := by omega
    _ ≤ M.wrap_left * M.evalStep s + (A + M.recur_counter * M.c_zero) := by
          exact Nat.add_le_add_right hleft (A + M.recur_counter * M.c_zero)
    _ ≤ M.wrap_left * M.evalStep s + M.wrap_right * (A + M.recur_counter * M.c_zero) := by
          exact Nat.add_le_add_left hright (M.wrap_left * M.evalStep s)
    _ ≤ M.wrap_const + M.wrap_left * M.evalStep s +
          M.wrap_right * (A + M.recur_counter * M.c_zero) := by
          omega

/-- The affine barrier also survives in the typed fragment once the step sort
admits an unbounded closed pump family. -/
theorem no_affine_orients_typed_recSucc_of_stepPump (M : AffineMeasure)
    (hpump : HasTypedStepPump M) :
    ¬ (∀ (b : Term .res) (s : Term .step) (n : Term .cnt),
      M.evalRes (wrap s (recur b s n)) < M.evalRes (recur b s (succ n))) := by
  intro h
  rcases hpump (typedAffineBound M) with ⟨s, hs⟩
  have hspec := h base s zero
  have hge := typed_affine_target_ge_source_of_bound M hs
  exact Nat.not_lt_of_ge hge hspec

end OperatorKO7.TypedBarrierSurvival
