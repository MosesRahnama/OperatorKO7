import OperatorKO7.Meta.CompositionalMeasure_Impossibility

/-!
RecΔ-core subsystem: the 4-constructor fragment `{void, delta, app, recΔ}`.

This file restates the compositional-impossibility boundary directly on the core
signature used by the counterexamples.
-/

namespace OperatorKO7.RecCore

open OperatorKO7

/-- RecΔ-core syntax (the 4-constructor fragment). -/
inductive RecCoreTerm : Type
| void : RecCoreTerm
| delta : RecCoreTerm → RecCoreTerm
| app : RecCoreTerm → RecCoreTerm → RecCoreTerm
| recΔ : RecCoreTerm → RecCoreTerm → RecCoreTerm → RecCoreTerm
deriving DecidableEq, Repr

open RecCoreTerm

/-- Canonical embedding of RecΔ-core terms into full KO7 traces. -/
@[simp] def embed : RecCoreTerm → Trace
  | RecCoreTerm.void         => Trace.void
  | RecCoreTerm.delta t      => Trace.delta (embed t)
  | RecCoreTerm.app a b      => Trace.app (embed a) (embed b)
  | RecCoreTerm.recΔ b s n   => Trace.recΔ (embed b) (embed s) (embed n)

/-- Iterated core app constructor used to pump measure size. -/
def appIter : Nat → RecCoreTerm
  | 0     => RecCoreTerm.void
  | k + 1 => RecCoreTerm.app (appIter k) RecCoreTerm.void

/-- Additive compositional measures restricted to RecΔ-core constructors. -/
structure AdditiveRecCoreMeasure where
  w_void      : Nat
  w_delta     : Nat
  w_app       : Nat
  w_rec       : Nat
  hw_app_pos  : w_app ≥ 1

/-- Evaluation for additive RecΔ-core measures. -/
@[simp] def AdditiveRecCoreMeasure.eval
    (M : AdditiveRecCoreMeasure) : RecCoreTerm → Nat
  | RecCoreTerm.void        => M.w_void
  | RecCoreTerm.delta t     => M.w_delta + M.eval t
  | RecCoreTerm.app a b     => M.w_app + M.eval a + M.eval b
  | RecCoreTerm.recΔ b s n  => M.w_rec + M.eval b + M.eval s + M.eval n

lemma eval_appIter_ge (M : AdditiveRecCoreMeasure) (k : Nat) :
    M.eval (appIter k) ≥ k := by
  induction k with
  | zero => simp [appIter, AdditiveRecCoreMeasure.eval]
  | succ k ih =>
      simp only [appIter, AdditiveRecCoreMeasure.eval]
      have := M.hw_app_pos
      omega

/-- Tier-1 impossibility specialized to RecΔ-core. -/
theorem no_additive_compositional_orients_rec_succ
    (M : AdditiveRecCoreMeasure) :
    ¬ (∀ (b s n : RecCoreTerm),
      M.eval (RecCoreTerm.app s (RecCoreTerm.recΔ b s n)) <
      M.eval (RecCoreTerm.recΔ b s (RecCoreTerm.delta n))) := by
  intro h
  have hspec := h RecCoreTerm.void (appIter M.w_delta) RecCoreTerm.void
  simp only [AdditiveRecCoreMeasure.eval] at hspec
  have hge := eval_appIter_ge M M.w_delta
  have := M.hw_app_pos
  omega

/-- Abstract compositional measures restricted to RecΔ-core constructors. -/
structure CompositionalRecCoreMeasure where
  c_void      : Nat
  c_delta     : Nat → Nat
  c_app       : Nat → Nat → Nat
  c_recΔ      : Nat → Nat → Nat → Nat
  app_subterm1 : ∀ x y, c_app x y > x
  app_subterm2 : ∀ x y, c_app x y > y

/-- Evaluation for abstract RecΔ-core compositional measures. -/
@[simp] def CompositionalRecCoreMeasure.eval
    (CM : CompositionalRecCoreMeasure) : RecCoreTerm → Nat
  | RecCoreTerm.void        => CM.c_void
  | RecCoreTerm.delta t     => CM.c_delta (CM.eval t)
  | RecCoreTerm.app a b     => CM.c_app (CM.eval a) (CM.eval b)
  | RecCoreTerm.recΔ b s n  => CM.c_recΔ (CM.eval b) (CM.eval s) (CM.eval n)

/-- Tier-2 impossibility specialized to RecΔ-core (transparent delta case). -/
theorem no_compositional_orients_rec_succ_transparent_delta
    (CM : CompositionalRecCoreMeasure)
    (h_transparent : CM.c_delta CM.c_void = CM.c_void) :
    ¬ (∀ (b s n : RecCoreTerm),
      CM.eval (RecCoreTerm.app s (RecCoreTerm.recΔ b s n)) <
      CM.eval (RecCoreTerm.recΔ b s (RecCoreTerm.delta n))) := by
  intro h
  have hspec :
      CM.c_app CM.c_void (CM.c_recΔ CM.c_void CM.c_void CM.c_void) <
      CM.c_recΔ CM.c_void CM.c_void CM.c_void := by
    simpa [CompositionalRecCoreMeasure.eval, h_transparent] using
      h RecCoreTerm.void RecCoreTerm.void RecCoreTerm.void
  have hsub := CM.app_subterm2 CM.c_void (CM.c_recΔ CM.c_void CM.c_void CM.c_void)
  omega

/-- DP-style projection on RecΔ-core (tracks only recursion counter depth). -/
@[simp] def dpProjection : RecCoreTerm → Nat
  | RecCoreTerm.void        => 0
  | RecCoreTerm.delta t     => dpProjection t + 1
  | RecCoreTerm.app _ _     => 0
  | RecCoreTerm.recΔ _ _ n  => dpProjection n

@[simp] theorem dpProjection_embed (t : RecCoreTerm) :
    OperatorKO7.CompositionalImpossibility.dpProjection (embed t) = dpProjection t := by
  induction t with
  | void => rfl
  | delta t ih => simp [embed, dpProjection, ih]
  | app a b iha ihb => simp [embed, dpProjection]
  | recΔ b s n ihb ihs ihn =>
      simpa [embed, dpProjection] using ihn

/-- DP projection orients the duplicating recursor on RecΔ-core. -/
theorem dp_projection_orients_rec_succ (b s n : RecCoreTerm) :
    dpProjection (RecCoreTerm.app s (RecCoreTerm.recΔ b s n)) <
    dpProjection (RecCoreTerm.recΔ b s (RecCoreTerm.delta n)) := by
  simp [dpProjection]

/-- DP projection violates app-subterm sensitivity on RecΔ-core. -/
theorem dp_projection_violates_sensitivity :
    ∃ x y : RecCoreTerm,
      ¬ (dpProjection (RecCoreTerm.app x y) > dpProjection x) := by
  exact ⟨RecCoreTerm.delta RecCoreTerm.void, RecCoreTerm.void, by simp [dpProjection]⟩

/-- DP projection also violates the second app-subterm condition. -/
theorem dp_projection_violates_subterm2 :
    ∃ x y : RecCoreTerm,
      ¬ (dpProjection (RecCoreTerm.app x y) > dpProjection y) := by
  exact ⟨RecCoreTerm.void, RecCoreTerm.delta RecCoreTerm.void, by simp [dpProjection]⟩

end OperatorKO7.RecCore
