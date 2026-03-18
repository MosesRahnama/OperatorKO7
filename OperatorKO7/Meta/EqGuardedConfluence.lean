import OperatorKO7.Kernel
import OperatorKO7.Meta.PolyInterpretation_FullStep
import OperatorKO7.Meta.SafeStep_Core

/-!
# Root confluence for an intermediate `eqW`-guarded fragment

This module isolates a fragment strictly between the guarded `SafeStep` relation
and the full unguarded root relation `Step`.

- all full KO7 root rules remain available,
- only the problematic `eqW` diff branch is guarded by disequality.

This removes the unique full-root confluence obstruction without importing the
termination-oriented merge / rec-zero guards from `SafeStep`.
-/

open Classical
open OperatorKO7 Trace

namespace OperatorKO7.EqGuardedConfluence

/-- Intermediate root relation: full `Step`, except that the `eqW` diff branch
is available only on distinct arguments. -/
inductive EqGuardedStep : Trace → Trace → Prop
| R_int_delta (t) : EqGuardedStep (integrate (delta t)) void
| R_merge_void_left (t) : EqGuardedStep (merge void t) t
| R_merge_void_right (t) : EqGuardedStep (merge t void) t
| R_merge_cancel (t) : EqGuardedStep (merge t t) t
| R_rec_zero (b s) : EqGuardedStep (recΔ b s void) b
| R_rec_succ (b s n) : EqGuardedStep (recΔ b s (delta n)) (app s (recΔ b s n))
| R_eq_refl (a) : EqGuardedStep (eqW a a) void
| R_eq_diff (a b) (hne : a ≠ b) : EqGuardedStep (eqW a b) (integrate (merge a b))

/-- Reverse relation for well-foundedness / Newman arguments. -/
def EqGuardedStepRev : Trace → Trace → Prop := fun a b => EqGuardedStep b a

/-- Reflexive-transitive closure of the intermediate fragment. -/
inductive EqGuardedStepStar : Trace → Trace → Prop
| refl : ∀ t, EqGuardedStepStar t t
| tail : ∀ {a b c}, EqGuardedStep a b → EqGuardedStepStar b c → EqGuardedStepStar a c

/-- Local joinability at a fixed source. -/
def LocalJoinEqGuarded (a : Trace) : Prop :=
  ∀ {b c}, EqGuardedStep a b → EqGuardedStep a c → ∃ d, EqGuardedStepStar b d ∧ EqGuardedStepStar c d

/-- Church-Rosser for the intermediate fragment. -/
def ConfluentEqGuarded : Prop :=
  ∀ a b c, EqGuardedStepStar a b → EqGuardedStepStar a c → ∃ d, EqGuardedStepStar b d ∧ EqGuardedStepStar c d

theorem eqgstar_trans {a b c : Trace}
    (h₁ : EqGuardedStepStar a b) (h₂ : EqGuardedStepStar b c) : EqGuardedStepStar a c := by
  induction h₁ with
  | refl => exact h₂
  | tail hab _ ih => exact EqGuardedStepStar.tail hab (ih h₂)

theorem eqgstar_destruct {a c : Trace} (h : EqGuardedStepStar a c) :
    a = c ∨ ∃ b, EqGuardedStep a b ∧ EqGuardedStepStar b c := by
  cases h with
  | refl t => exact Or.inl rfl
  | tail hab hbc => exact Or.inr ⟨_, hab, hbc⟩

/-- The intermediate fragment is a subrelation of the full root relation. -/
theorem eqGuarded_sub_step : ∀ {a b : Trace}, EqGuardedStep a b → Step a b
  | _, _, EqGuardedStep.R_int_delta t => Step.R_int_delta t
  | _, _, EqGuardedStep.R_merge_void_left t => Step.R_merge_void_left t
  | _, _, EqGuardedStep.R_merge_void_right t => Step.R_merge_void_right t
  | _, _, EqGuardedStep.R_merge_cancel t => Step.R_merge_cancel t
  | _, _, EqGuardedStep.R_rec_zero b s => Step.R_rec_zero b s
  | _, _, EqGuardedStep.R_rec_succ b s n => Step.R_rec_succ b s n
  | _, _, EqGuardedStep.R_eq_refl a => Step.R_eq_refl a
  | _, _, EqGuardedStep.R_eq_diff a b _ => Step.R_eq_diff a b

/-- Full-step termination already bounds the intermediate fragment. -/
theorem wf_EqGuardedStepRev : WellFounded EqGuardedStepRev := by
  have hsub : Subrelation EqGuardedStepRev (fun a b : Trace => Step b a) := by
    intro a b hab
    exact eqGuarded_sub_step hab
  exact Subrelation.wf hsub OperatorKO7.PolyInterpretation.wf_StepRev_poly

/-- `SafeStep` embeds into the intermediate fragment. -/
theorem safeStep_sub_eqGuarded : ∀ {a b : Trace}, MetaSN_KO7.SafeStep a b → EqGuardedStep a b
  | _, _, MetaSN_KO7.SafeStep.R_int_delta t => EqGuardedStep.R_int_delta t
  | _, _, MetaSN_KO7.SafeStep.R_merge_void_left t _ => EqGuardedStep.R_merge_void_left t
  | _, _, MetaSN_KO7.SafeStep.R_merge_void_right t _ => EqGuardedStep.R_merge_void_right t
  | _, _, MetaSN_KO7.SafeStep.R_merge_cancel t _ _ => EqGuardedStep.R_merge_cancel t
  | _, _, MetaSN_KO7.SafeStep.R_rec_zero b s _ => EqGuardedStep.R_rec_zero b s
  | _, _, MetaSN_KO7.SafeStep.R_rec_succ b s n => EqGuardedStep.R_rec_succ b s n
  | _, _, MetaSN_KO7.SafeStep.R_eq_refl a _ => EqGuardedStep.R_eq_refl a
  | _, _, MetaSN_KO7.SafeStep.R_eq_diff a b hne => EqGuardedStep.R_eq_diff a b hne

/-- The intermediate fragment is strictly larger than `SafeStep`: a blocked merge-void
step is restored because the extra guard is purely termination-oriented. -/
theorem eqGuarded_not_subset_safe :
    EqGuardedStep (merge void (recΔ void void (delta void))) (recΔ void void (delta void)) ∧
    ¬ MetaSN_KO7.SafeStep (merge void (recΔ void void (delta void))) (recΔ void void (delta void)) := by
  refine ⟨EqGuardedStep.R_merge_void_left _, ?_⟩
  intro h
  cases h with
  | R_merge_void_left _ hδ =>
      simp [MetaSN_KO7.deltaFlag] at hδ

/-- The intermediate fragment is root-deterministic up to target equality. -/
theorem eqGuarded_unique_target {a b c : Trace}
    (hb : EqGuardedStep a b) (hc : EqGuardedStep a c) : b = c := by
  cases hb <;> cases hc <;> simp at *

/-- Local joinability is immediate from unique targets. -/
theorem localJoin_all_eqGuarded : ∀ a : Trace, LocalJoinEqGuarded a := by
  intro a b c hb hc
  refine ⟨b, EqGuardedStepStar.refl b, ?_⟩
  simpa [eqGuarded_unique_target hb hc] using (EqGuardedStepStar.refl b : EqGuardedStepStar b b)

private theorem join_star_star_at
    (locAll : ∀ a, LocalJoinEqGuarded a) :
    ∀ x, Acc EqGuardedStepRev x →
      ∀ {y z : Trace}, EqGuardedStepStar x y → EqGuardedStepStar x z →
        ∃ d, EqGuardedStepStar y d ∧ EqGuardedStepStar z d := by
  intro x hx
  induction hx with
  | intro x _ ih =>
      intro y z hxy hxz
      have HY := eqgstar_destruct hxy
      have HZ := eqgstar_destruct hxz
      cases HY with
      | inl hEq =>
          cases hEq
          exact ⟨z, hxz, EqGuardedStepStar.refl z⟩
      | inr hy =>
          rcases hy with ⟨b1, hxb1, hb1y⟩
          cases HZ with
          | inl hEq2 =>
              cases hEq2
              exact ⟨y, EqGuardedStepStar.refl y, EqGuardedStepStar.tail hxb1 hb1y⟩
          | inr hz =>
              rcases hz with ⟨c1, hxc1, hc1z⟩
              rcases locAll x hxb1 hxc1 with ⟨e, hb1e, hc1e⟩
              rcases ih c1 hxc1 hc1e hc1z with ⟨d₁, hed₁, hzd₁⟩
              have hb1d₁ : EqGuardedStepStar b1 d₁ := eqgstar_trans hb1e hed₁
              rcases ih b1 hxb1 hb1y hb1d₁ with ⟨d, hyd, hd₁d⟩
              exact ⟨d, hyd, eqgstar_trans hzd₁ hd₁d⟩

/-- Newman specialization for the intermediate fragment. -/
theorem confluentEqGuarded : ConfluentEqGuarded := by
  intro a b c hab hac
  exact join_star_star_at localJoin_all_eqGuarded a (wf_EqGuardedStepRev.apply a) hab hac

end OperatorKO7.EqGuardedConfluence
