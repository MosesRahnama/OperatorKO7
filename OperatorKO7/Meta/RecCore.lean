import OperatorKO7.Meta.CompositionalMeasure_Impossibility

/-!
RecΔ-core subsystem: the 4-constructor fragment `{void, delta, app, recΔ}`.

This file restates the compositional-impossibility boundary directly on the core
signature used by the counterexamples.
-/

namespace OperatorKO7.RecCore

open OperatorKO7
open OperatorKO7.StepDuplicating

/-- RecΔ-core syntax (the 4-constructor fragment). -/
inductive RecCoreTerm : Type
| void : RecCoreTerm
| delta : RecCoreTerm → RecCoreTerm
| app : RecCoreTerm → RecCoreTerm → RecCoreTerm
| recΔ : RecCoreTerm → RecCoreTerm → RecCoreTerm → RecCoreTerm
deriving DecidableEq, Repr

open RecCoreTerm

/-- The RecΔ-core schema instance of the generic duplication barrier. -/
def recCoreSchema : StepDuplicatingSchema where
  T := RecCoreTerm
  base := RecCoreTerm.void
  succ := RecCoreTerm.delta
  wrap := RecCoreTerm.app
  recur := RecCoreTerm.recΔ

/-- Canonical embedding of RecΔ-core terms into full KO7 traces. -/
@[simp] def embed : RecCoreTerm → Trace
  | RecCoreTerm.void         => Trace.void
  | RecCoreTerm.delta t      => Trace.delta (embed t)
  | RecCoreTerm.app a b      => Trace.app (embed a) (embed b)
  | RecCoreTerm.recΔ b s n   => Trace.recΔ (embed b) (embed s) (embed n)

/-- Iterated core app constructor used to pump measure size. -/
def appIter : Nat → RecCoreTerm :=
  StepDuplicatingSchema.wrapIter recCoreSchema

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

/-- Generic-schema view of an additive RecΔ-core measure. -/
def AdditiveRecCoreMeasure.toSchemaMeasure
    (M : AdditiveRecCoreMeasure) :
    StepDuplicatingSchema.AdditiveMeasure recCoreSchema where
  eval := M.eval
  w_base := M.w_void
  w_succ := M.w_delta
  w_wrap := M.w_app
  w_recur := M.w_rec
  eval_base := by rfl
  eval_succ := by intro t; rfl
  eval_wrap := by intro x y; rfl
  eval_recur := by intro b s n; rfl
  h_wrap_pos := M.hw_app_pos

lemma eval_appIter_ge (M : AdditiveRecCoreMeasure) (k : Nat) :
    M.eval (appIter k) ≥ k := by
  simpa [appIter, AdditiveRecCoreMeasure.toSchemaMeasure] using
    (StepDuplicatingSchema.eval_wrapIter_ge
      (S := recCoreSchema) (M := M.toSchemaMeasure) k)

/-- Tier-1 impossibility specialized to RecΔ-core. -/
theorem no_additive_compositional_orients_rec_succ
    (M : AdditiveRecCoreMeasure) :
    ¬ (∀ (b s n : RecCoreTerm),
      M.eval (RecCoreTerm.app s (RecCoreTerm.recΔ b s n)) <
      M.eval (RecCoreTerm.recΔ b s (RecCoreTerm.delta n))) := by
  simpa [recCoreSchema, AdditiveRecCoreMeasure.toSchemaMeasure] using
    (StepDuplicatingSchema.no_additive_orients_dup_step
      (S := recCoreSchema) (M := M.toSchemaMeasure))

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

/-- Generic-schema view of an abstract RecΔ-core compositional measure. -/
def CompositionalRecCoreMeasure.toSchemaMeasure
    (CM : CompositionalRecCoreMeasure) :
    StepDuplicatingSchema.CompositionalMeasure recCoreSchema where
  eval := CM.eval
  c_base := CM.c_void
  c_succ := CM.c_delta
  c_wrap := CM.c_app
  c_recur := CM.c_recΔ
  eval_base := by rfl
  eval_succ := by intro t; rfl
  eval_wrap := by intro x y; rfl
  eval_recur := by intro b s n; rfl
  wrap_subterm1 := CM.app_subterm1
  wrap_subterm2 := CM.app_subterm2

/-- Tier-2 impossibility specialized to RecΔ-core (transparent delta case). -/
theorem no_compositional_orients_rec_succ_transparent_delta
    (CM : CompositionalRecCoreMeasure)
    (h_transparent : CM.c_delta CM.c_void = CM.c_void) :
    ¬ (∀ (b s n : RecCoreTerm),
      CM.eval (RecCoreTerm.app s (RecCoreTerm.recΔ b s n)) <
      CM.eval (RecCoreTerm.recΔ b s (RecCoreTerm.delta n))) := by
  simpa [recCoreSchema, CompositionalRecCoreMeasure.toSchemaMeasure] using
    (StepDuplicatingSchema.no_compositional_orients_dup_step_transparent_succ
      (S := recCoreSchema) (CM := CM.toSchemaMeasure) h_transparent)

/-- DP-style projection on RecΔ-core (tracks only recursion counter depth). -/
@[simp] def dpProjection : RecCoreTerm → Nat
  | RecCoreTerm.void        => 0
  | RecCoreTerm.delta t     => dpProjection t + 1
  | RecCoreTerm.app _ _     => 0
  | RecCoreTerm.recΔ _ _ n  => dpProjection n

/-- RecΔ-core DP projection as a generic schema rank. -/
def dpProjectionRank : StepDuplicatingSchema.ProjectionRank recCoreSchema where
  rank := dpProjection
  rank_base := by rfl
  rank_succ := by intro t; rfl
  rank_wrap := by intro x y; rfl
  rank_recur := by intro b s n; rfl

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
  exact
    (StepDuplicatingSchema.projection_orients_dup_step
      (S := recCoreSchema) dpProjectionRank b s n)

/-- DP projection violates app-subterm sensitivity on RecΔ-core. -/
theorem dp_projection_violates_sensitivity :
    ∃ x y : RecCoreTerm,
      ¬ (dpProjection (RecCoreTerm.app x y) > dpProjection x) := by
  simpa [recCoreSchema, dpProjectionRank] using
    (StepDuplicatingSchema.projection_violates_wrap_subterm1
      (S := recCoreSchema) dpProjectionRank)

/-- DP projection also violates the second app-subterm condition. -/
theorem dp_projection_violates_subterm2 :
    ∃ x y : RecCoreTerm,
      ¬ (dpProjection (RecCoreTerm.app x y) > dpProjection y) := by
  simpa [recCoreSchema, dpProjectionRank] using
    (StepDuplicatingSchema.projection_violates_wrap_subterm2
      (S := recCoreSchema) dpProjectionRank)

/-- Concrete nonlinear witness showing that Tier-2 transparency is essential. -/
def quadraticWitness : CompositionalRecCoreMeasure where
  c_void := 1
  c_delta := fun x => x + 1
  c_app := fun x y => x + y + 1
  c_recΔ := fun a b c => a + b * (c + 1) * (c + 1) + c
  app_subterm1 := by
    intro x y
    omega
  app_subterm2 := by
    intro x y
    omega

/-- Every term has positive value under the nonlinear witness. -/
lemma quadraticWitness_eval_pos (t : RecCoreTerm) :
    1 ≤ quadraticWitness.eval t := by
  induction t with
  | void =>
      simp [quadraticWitness]
  | delta t ih =>
      show 1 ≤ quadraticWitness.eval (RecCoreTerm.delta t)
      simp [CompositionalRecCoreMeasure.eval, quadraticWitness]
  | app a b iha ihb =>
      show 1 ≤ quadraticWitness.eval (RecCoreTerm.app a b)
      simp [CompositionalRecCoreMeasure.eval, quadraticWitness]
  | recΔ b s n ihb ihs ihn =>
      have h :
          quadraticWitness.eval b ≤
            quadraticWitness.eval b +
              quadraticWitness.eval s * (quadraticWitness.eval n + 1) *
                (quadraticWitness.eval n + 1) +
              quadraticWitness.eval n := by
        omega
      simpa [CompositionalRecCoreMeasure.eval, quadraticWitness] using le_trans ihb h

/-- The nonlinear witness is not transparent at the base term. -/
lemma quadraticWitness_not_transparent :
    quadraticWitness.c_delta quadraticWitness.c_void ≠ quadraticWitness.c_void := by
  simp [quadraticWitness]

/-- The nonlinear witness strictly orients the duplicating recursor step. -/
theorem quadraticWitness_orients_rec_succ (b s n : RecCoreTerm) :
    quadraticWitness.eval (RecCoreTerm.app s (RecCoreTerm.recΔ b s n)) <
      quadraticWitness.eval (RecCoreTerm.recΔ b s (RecCoreTerm.delta n)) := by
  set B := quadraticWitness.eval b
  set S := quadraticWitness.eval s
  set N := quadraticWitness.eval n
  have hs : 1 ≤ S := by
    simpa [S] using quadraticWitness_eval_pos s
  have hn : 1 ≤ N := by
    simpa [N] using quadraticWitness_eval_pos n
  have hmain : S + S * (N + 1) * (N + 1) < S * (N + 2) * (N + 2) := by
    nlinarith
  have hcalc :
      S + (B + S * (N + 1) * (N + 1) + N) + 1 <
        B + S * (N + 2) * (N + 2) + (N + 1) := by
    nlinarith [hmain]
  simpa [B, S, N, CompositionalRecCoreMeasure.eval, quadraticWitness] using hcalc

/-- The nonlinear witness satisfies the RecΔ-core compositional axioms but lies
outside Tier 2 exactly because transparency fails. -/
theorem quadraticWitness_exhibits_transparency_gap :
    (∀ x y, quadraticWitness.c_app x y > x) ∧
    (∀ x y, quadraticWitness.c_app x y > y) ∧
    quadraticWitness.c_delta quadraticWitness.c_void ≠ quadraticWitness.c_void ∧
    (∀ b s n : RecCoreTerm,
      quadraticWitness.eval (RecCoreTerm.app s (RecCoreTerm.recΔ b s n)) <
        quadraticWitness.eval (RecCoreTerm.recΔ b s (RecCoreTerm.delta n))) := by
  refine ⟨quadraticWitness.app_subterm1, quadraticWitness.app_subterm2,
    quadraticWitness_not_transparent, ?_⟩
  intro b s n
  exact quadraticWitness_orients_rec_succ b s n

/-- The Tier-2 transparency hypothesis is essential on RecΔ-core:
there exists a compositional measure satisfying the wrapper-subterm axioms,
failing transparency at `void`, and still orienting the duplicating step. -/
theorem transparency_is_essential_for_tier2 :
    ∃ CM : CompositionalRecCoreMeasure,
      (∀ x y, CM.c_app x y > x) ∧
      (∀ x y, CM.c_app x y > y) ∧
      CM.c_delta CM.c_void ≠ CM.c_void ∧
      (∀ b s n : RecCoreTerm,
        CM.eval (RecCoreTerm.app s (RecCoreTerm.recΔ b s n)) <
          CM.eval (RecCoreTerm.recΔ b s (RecCoreTerm.delta n))) := by
  exact ⟨quadraticWitness, quadraticWitness_exhibits_transparency_gap⟩

end OperatorKO7.RecCore
