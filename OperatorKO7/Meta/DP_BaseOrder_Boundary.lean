import OperatorKO7.Meta.DependencyPairs_Works

/-!
# Dependency-Pair Base-Order Boundary

The extracted KO7 dependency-pair problem is a single predecessor drop on the
recursor counter:

`recΔ b s (delta n) ↦ recΔ b s n`.

This file records the key boundary fact: the pair problem is already oriented by
a very simple linear polynomial-style base order. Therefore there is no blanket
negative theorem saying that dependency pairs still fail whenever the base order
is affine or polynomial.
-/

open OperatorKO7 Trace

namespace OperatorKO7.DPBaseOrderBoundary

open MetaSN_KO7
open OperatorKO7.MetaDependencyPairs

/-- Counter-height measure used as a simple linear polynomial-style DP base order. -/
@[simp] def counterHeight : Trace → Nat
  | void => 0
  | delta t => counterHeight t + 1
  | integrate t => counterHeight t
  | merge a b => counterHeight a + counterHeight b
  | app a b => counterHeight a + counterHeight b
  | recΔ _ _ n => counterHeight n
  | eqW a b => counterHeight a + counterHeight b

/-- The extracted KO7 dependency-pair problem is oriented by `counterHeight`. -/
theorem counterHeight_orients_dpPair :
    ∀ {a b : Trace}, DPPair a b → counterHeight b < counterHeight a
  | _, _, DPPair.rec_succ _ _ n => by
      simp [counterHeight]

/-- There exists a concrete linear polynomial-style base order orienting the extracted
dependency-pair problem. -/
theorem extracted_dp_problem_has_linear_base_order :
    ∃ μ : Trace → Nat, ∀ {a b : Trace}, DPPair a b → μ b < μ a := by
  exact ⟨counterHeight, fun {_ _} h => counterHeight_orients_dpPair h⟩

/-- Therefore the hoped-for blanket barrier against affine/polynomial DP base orders is
false for the extracted KO7 dependency-pair problem. -/
theorem no_blanket_dp_poly_base_barrier :
    ¬ (∀ μ : Trace → Nat, (∀ {a b : Trace}, DPPair a b → μ b < μ a) → False) := by
  intro h
  rcases extracted_dp_problem_has_linear_base_order with ⟨μ, hμ⟩
  exact h μ hμ

end OperatorKO7.DPBaseOrderBoundary
