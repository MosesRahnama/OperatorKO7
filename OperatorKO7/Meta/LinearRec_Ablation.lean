import OperatorKO7.Kernel

namespace OperatorKO7

/-!
# Feature-4 Ablation: Linear (Non-Duplicating) Recursor

This module proves that removing step duplication (barrier condition 4)
dissolves the global orientation barrier. We define a linear recursor variant
where the step argument `s` is not duplicated on the RHS of `rec_succ`
(the RHS is `recΔ b s n` instead of `app s (recΔ b s n)`), and show that
`simpleSize` (a Tier-1 additive compositional measure) strictly orients both
rules.

This confirms: the barrier is caused by duplication, not by the recursor
pattern itself.
-/

open Trace

/-! ## Linear recursor step relation -/

/-- A non-duplicating recursor: `recΔ b s (delta n) → recΔ b s n`.
    The step argument `s` is **not** duplicated on the RHS. -/
inductive LinearStep : Trace → Trace → Prop
| R_rec_zero_linear : ∀ b s, LinearStep (recΔ b s void) b
| R_rec_succ_linear : ∀ b s n, LinearStep (recΔ b s (delta n)) (recΔ b s n)

/-! ## simpleSize: a Tier-1 additive compositional measure -/

/-- Node count: every constructor contributes 1 plus the sum of its subterms. -/
def simpleSize : Trace → Nat
| void => 1
| delta t => 1 + simpleSize t
| integrate t => 1 + simpleSize t
| merge a b => 1 + simpleSize a + simpleSize b
| app a b => 1 + simpleSize a + simpleSize b
| recΔ b s n => 1 + simpleSize b + simpleSize s + simpleSize n
| eqW a b => 1 + simpleSize a + simpleSize b

/-- `simpleSize` is always positive. -/
theorem simpleSize_pos (t : Trace) : 0 < simpleSize t := by
  cases t <;> simp [simpleSize] <;> omega

/-! ## Strict orientation theorems -/

/-- `simpleSize` strictly orients `R_rec_zero_linear`:
    `simpleSize b < simpleSize (recΔ b s void)` -/
theorem simpleSize_orients_rec_zero_linear (b s : Trace) :
    simpleSize b < simpleSize (recΔ b s void) := by
  simp [simpleSize]; omega

/-- `simpleSize` strictly orients `R_rec_succ_linear`:
    `simpleSize (recΔ b s n) < simpleSize (recΔ b s (delta n))` -/
theorem simpleSize_orients_rec_succ_linear (b s n : Trace) :
    simpleSize (recΔ b s n) < simpleSize (recΔ b s (delta n)) := by
  simp [simpleSize]

/-- Every `LinearStep` instance is strictly oriented by `simpleSize`. -/
theorem simpleSize_orients_linearStep {a b : Trace} (h : LinearStep a b) :
    simpleSize b < simpleSize a := by
  cases h with
  | R_rec_zero_linear b s => exact simpleSize_orients_rec_zero_linear b s
  | R_rec_succ_linear b s n => exact simpleSize_orients_rec_succ_linear b s n

/-- Strong normalization of `LinearStep` via `simpleSize`. -/
theorem wf_linearStep : WellFounded (fun a b => LinearStep b a) :=
  Subrelation.wf
    (fun {_ _} h => simpleSize_orients_linearStep h)
    (InvImage.wf simpleSize Nat.lt_wfRel.wf)

/-! ## Contrast: the duplicating recursor cannot be oriented by simpleSize -/

/-- Witness: `simpleSize` does **not** strictly orient the duplicating
    `R_rec_succ` for all instantiations. Specifically, for `b = void`,
    `s = app void void`, `n = void`, the RHS is strictly larger. -/
theorem simpleSize_fails_on_duplicating_rec_succ :
    ¬ (∀ b s n, simpleSize (app s (recΔ b s n)) < simpleSize (recΔ b s (delta n))) := by
  intro h
  have := h void (app void void) void
  simp [simpleSize] at this

end OperatorKO7
