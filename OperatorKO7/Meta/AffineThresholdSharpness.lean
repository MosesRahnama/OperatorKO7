import OperatorKO7.Meta.StepDuplicatingSchema

/-!
# Sharpness of the affine pump bound

The generic affine barrier uses the contradiction bound

`recur_counter * (succ_bias + succ_scale * c_base)`.

This module shows that the bound is not merely a proof artifact: there is a
canonical affine family for which the bound is exact. Below the bound, the
distinguished duplicating-step instance is strictly oriented; at the bound, the
strict inequality fails.
-/

namespace OperatorKO7.StepDuplicating
open StepDuplicatingSchema

/-- A canonical schema over `Nat` used to witness sharpness of the affine pump
bound. The recursor ignores `base` and `step` payloads and scales only the
counter. -/
def affineThresholdSchema (t : Nat) : StepDuplicatingSchema where
  T := Nat
  base := 0
  succ := fun _ => 1
  wrap := Nat.add
  recur := fun _ _ n => t * n

/-- A canonical affine measure on `affineThresholdSchema t` whose barrier bound
is exactly `t`. -/
def affineThresholdMeasure (t : Nat) : AffineMeasure (affineThresholdSchema t) where
  eval := id
  c_base := 0
  succ_bias := 1
  succ_scale := 0
  wrap_const := 0
  wrap_left := 1
  wrap_right := 1
  recur_const := 0
  recur_base := 0
  recur_step := 0
  recur_counter := t
  eval_base := rfl
  eval_succ := by
    intro n
    simp [affineThresholdSchema]
  eval_wrap := by
    intro x y
    simp [affineThresholdSchema]
  eval_recur := by
    intro b s n
    simp [affineThresholdSchema]
  h_wrap_left_pos := by decide
  h_wrap_right_pos := by decide

/-- The generic affine contradiction bound specializes to `t` on the canonical
sharpness family. -/
theorem affineThresholdMeasure_bound (t : Nat) :
    (affineThresholdMeasure t).recur_counter *
        ((affineThresholdMeasure t).succ_bias +
          (affineThresholdMeasure t).succ_scale * (affineThresholdMeasure t).c_base) = t := by
  simp [affineThresholdMeasure]

/-- On the canonical sharpness family, the distinguished root-step inequality is
equivalent to the strict inequality `k < t`. -/
theorem affineThresholdMeasure_exact_cutoff (t k : Nat) :
    let S := affineThresholdSchema t
    let M := affineThresholdMeasure t
    M.eval (S.wrap k (S.recur S.base k S.base)) <
      M.eval (S.recur S.base k (S.succ S.base)) ↔
        k < (M.recur_counter * (M.succ_bias + M.succ_scale * M.c_base)) := by
  simp [affineThresholdSchema, affineThresholdMeasure]

/-- Below the generic affine contradiction bound, the canonical family strictly
orients the distinguished root-step instance. -/
theorem affineThresholdMeasure_orients_below_bound {t k : Nat} (hk : k < t) :
    let S := affineThresholdSchema t
    let M := affineThresholdMeasure t
    M.eval (S.wrap k (S.recur S.base k S.base)) <
      M.eval (S.recur S.base k (S.succ S.base)) := by
  simp [affineThresholdSchema, affineThresholdMeasure, hk]

/-- At the generic affine contradiction bound, the canonical family no longer
strictly orients the distinguished root-step instance. -/
theorem affineThresholdMeasure_fails_at_bound (t : Nat) :
    let S := affineThresholdSchema t
    let M := affineThresholdMeasure t
    ¬ M.eval (S.wrap t (S.recur S.base t S.base)) <
      M.eval (S.recur S.base t (S.succ S.base)) := by
  simp [affineThresholdSchema, affineThresholdMeasure]

end OperatorKO7.StepDuplicating
