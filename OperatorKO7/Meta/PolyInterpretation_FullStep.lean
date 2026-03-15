import OperatorKO7.Kernel
import Mathlib.Order.WellFounded
import Mathlib.Tactic.Linarith

/-!
# Nonlinear Polynomial Interpretation for the Full KO7 System

This module defines a nonlinear polynomial interpretation `W : Trace → Nat`
that strictly orients all 8 KO7 root rules.  This demonstrates that the
full unguarded system is terminating by a direct global measure—provided
the measure lies outside every formalized barrier class.

The interpretation uses:
- `W(recΔ b s n) = (W(n) + 1) * (W(s) + W(b) + 1)` — nonlinear coupling
- `W(delta t) = W(t) + 1` — non-transparent (≠ W(t))

These two properties place `W` outside:
- Tier 1 (additivity violated by the multiplicative recursor)
- Tier 2 (δ-transparency violated: W(δ t) = W(t)+1 ≠ W(t))
- Affine class (linearity violated by the cross-term product)

The barrier theorems predict exactly this: any measure that orients the
duplicating step must import structural assumptions outside the formalized
classes.  This module provides a machine-checked witness confirming the
barrier's precision (Remark 4.5 of the paper).
-/

namespace OperatorKO7.PolyInterpretation

open OperatorKO7 Trace

/-- Nonlinear polynomial interpretation over positive integers (≥ 1).
    The critical feature is the multiplicative recursor combiner:
    `(counter + 1) * (payload)`, which absorbs the duplication cost. -/
@[simp] def W : Trace → Nat
| void          => 1
| delta t       => W t + 1
| integrate t   => W t + 1
| merge a b     => W a + W b + 1
| app a b       => W a + W b + 1
| recΔ b s n    => (W n + 1) * (W s + W b + 1)
| eqW a b       => W a + W b + 3

/-- Every term has weight ≥ 1. -/
theorem W_pos (t : Trace) : 1 ≤ W t := by
  induction t with
  | void =>
      simp [W]
  | delta _ ih => simp only [W]; omega
  | integrate _ ih => simp only [W]; omega
  | merge _ _ iha ihb => simp only [W]; omega
  | app _ _ iha ihb => simp only [W]; omega
  | recΔ b s n ihb ihs ihn =>
      have hn : 1 ≤ W n + 1 := by omega
      have hs : 1 ≤ W s + W b + 1 := by omega
      have hmul : 1 * 1 ≤ (W n + 1) * (W s + W b + 1) :=
        Nat.mul_le_mul hn hs
      simpa [W] using hmul
  | eqW _ _ iha ihb => simp only [W]; omega

/-- The polynomial interpretation strictly orients every full-kernel Step.
    This is the main theorem: all 8 root rules are oriented by W. -/
theorem W_orients_step : ∀ {a b : Trace}, Step a b → W b < W a
  | _, _, Step.R_int_delta t => by
      simp only [W]
      omega
  | _, _, Step.R_merge_void_left t => by
      simp only [W]
      omega
  | _, _, Step.R_merge_void_right t => by
      simp only [W]
      omega
  | _, _, Step.R_merge_cancel t => by
      have ht := W_pos t
      simp only [W]
      omega
  | _, _, Step.R_rec_zero b s => by
      have hs := W_pos s
      have hb := W_pos b
      simp only [W]
      nlinarith
  | _, _, Step.R_rec_succ b s n => by
      have hb := W_pos b
      simp only [W]
      nlinarith
  | _, _, Step.R_eq_refl a => by
      have ha := W_pos a
      simp only [W]
      omega
  | _, _, Step.R_eq_diff a b => by
      simp only [W]
      omega

/-- Any relation on traces whose steps strictly decrease `W` is well-founded in reverse. -/
theorem wellFounded_of_W_decreases
    {R : Trace → Trace → Prop}
    (hdec : ∀ {a b : Trace}, R a b → W b < W a) :
    WellFounded (fun a b : Trace => R b a) := by
  have wf_measure : WellFounded (fun x y : Trace => W x < W y) :=
    InvImage.wf (f := W) Nat.lt_wfRel.wf
  have hsub : Subrelation (fun a b : Trace => R b a) (fun x y : Trace => W x < W y) := by
    intro x y hxy
    exact hdec hxy
  exact Subrelation.wf hsub wf_measure

/-- Full root-step KO7 termination from the nonlinear polynomial interpretation. -/
theorem wf_StepRev_poly : WellFounded (fun a b : Trace => Step b a) := by
  exact wellFounded_of_W_decreases (R := Step) (fun {_ _} h => W_orients_step h)

-- ============================================================
-- Axiom-violation witnesses: W lies outside every barrier class
-- ============================================================

/-- W violates δ-transparency: W(delta void) ≠ W(void). -/
theorem W_violates_transparency : W (delta void) ≠ W void := by
  simp [W]

/-- W is not additive: no constant c satisfies
    W(recΔ b s n) = c + W(b) + W(s) + W(n) for all terms. -/
theorem W_not_additive :
    ¬ ∃ c : Nat, ∀ b s n : Trace,
      W (recΔ b s n) = c + W b + W s + W n := by
  intro ⟨c, h⟩
  have h1 := h void void void
  have h2 := h void void (delta void)
  simp [W] at h1 h2
  omega

/-- W is not affine: no constants α, β, γ, δ_r satisfy
    W(recΔ b s n) = α + β·W(b) + γ·W(s) + δ_r·W(n) for all terms. -/
theorem W_not_affine :
    ¬ ∃ α β γ δ_r : Nat, ∀ b s n : Trace,
      W (recΔ b s n) = α + β * W b + γ * W s + δ_r * W n := by
  intro ⟨α, β, γ, δ_r, h⟩
  have h1 := h void void void
  have h2 := h void void (delta void)
  have h3 := h void (delta void) void
  have h4 := h (delta void) void void
  simp [W] at h1 h2 h3 h4
  omega

end OperatorKO7.PolyInterpretation
