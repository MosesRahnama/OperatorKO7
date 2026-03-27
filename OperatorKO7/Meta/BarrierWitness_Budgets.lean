import OperatorKO7.Meta.BarrierWitness_Extended

/-!
# Canonical budgets for constructive barrier witnesses

The generic schema-level witness extractors live over an abstract carrier `S.T`,
so they do not support a uniform theorem about concrete syntax size. Instead,
the file proves an explicit construction-budget theorem: the generated step payload is
always either the base term, a successor chain `succIter k`, or a wrapper chain
`wrapIter k`, with a computable budget `k` read off from the measure data.
-/

namespace OperatorKO7.StepDuplicating
open StepDuplicatingSchema

namespace StepDuplicatingSchema

/-- Canonical shapes used by the constructive schema-level witness extractors. -/
inductive WitnessStepShape (S : StepDuplicatingSchema) where
  | base
  | succPump (k : Nat)
  | wrapPump (k : Nat)

/-- Realization relation for the canonical witness shapes. -/
def WitnessStepShape.Realizes {S : StepDuplicatingSchema} :
    WitnessStepShape S → S.T → Prop
  | .base, t => t = S.base
  | .succPump k, t => t = succIter S k
  | .wrapPump k, t => t = wrapIter S k

theorem additive_witness_shape {S : StepDuplicatingSchema} (M : AdditiveMeasure S) :
    WitnessStepShape.Realizes
      (S := S) (.wrapPump M.w_succ) (additive_witness M).s := by
  rfl

theorem compositional_witness_shape {S : StepDuplicatingSchema}
    (CM : CompositionalMeasure S) (h_transparent : CM.c_succ CM.c_base = CM.c_base) :
    WitnessStepShape.Realizes
      (S := S) .base (compositional_witness CM h_transparent).s := by
  rfl

theorem affine_with_pump_witness_shape {S : StepDuplicatingSchema}
    (M : AffineMeasureWithPump S) :
    WitnessStepShape.Realizes
        (S := S)
        (.succPump (M.recur_counter * (M.succ_bias + M.succ_scale * M.c_base)))
        (affine_with_pump_witness M).s
      ∨
      WitnessStepShape.Realizes
        (S := S)
        (.wrapPump (M.recur_counter * (M.succ_bias + M.succ_scale * M.c_base)))
        (affine_with_pump_witness M).s := by
  classical
  by_cases hsucc : 1 ≤ M.succ_bias ∧ 1 ≤ M.succ_scale
  · left
    unfold affine_with_pump_witness
    simp only [hsucc]
    rfl
  · right
    unfold affine_with_pump_witness
    simp only [hsucc, dite_false]
    rfl

theorem quadratic_with_pump_witness_shape {S : StepDuplicatingSchema}
    (M : QuadraticCounterMeasureWithPump S) :
    WitnessStepShape.Realizes
        (S := S)
        (.succPump
          (M.recur_counter * (M.succ_bias + M.succ_scale * M.c_base) +
            M.recur_quad * (M.succ_bias + M.succ_scale * M.c_base) *
              (M.succ_bias + M.succ_scale * M.c_base)))
        (quadratic_with_pump_witness M).s
      ∨
      WitnessStepShape.Realizes
        (S := S)
        (.wrapPump
          (M.recur_counter * (M.succ_bias + M.succ_scale * M.c_base) +
            M.recur_quad * (M.succ_bias + M.succ_scale * M.c_base) *
              (M.succ_bias + M.succ_scale * M.c_base)))
        (quadratic_with_pump_witness M).s := by
  classical
  by_cases hsucc : 1 ≤ M.succ_bias ∧ 1 ≤ M.succ_scale
  · left
    unfold quadratic_with_pump_witness
    simp only [hsucc]
    rfl
  · right
    unfold quadratic_with_pump_witness
    simp only [hsucc, dite_false]
    rfl

theorem max_with_pump_witness_shape {S : StepDuplicatingSchema}
    (M : MaxMeasureWithPump S) :
    WitnessStepShape.Realizes
        (S := S)
        (.succPump (max (M.recur_base + M.c_base) (M.recur_counter + (M.succ_const + M.c_base))))
        (max_with_pump_witness M).s
      ∨
      WitnessStepShape.Realizes
        (S := S)
        (.wrapPump (max (M.recur_base + M.c_base) (M.recur_counter + (M.succ_const + M.c_base))))
        (max_with_pump_witness M).s := by
  classical
  by_cases hsucc : 1 ≤ M.succ_const
  · left
    unfold max_with_pump_witness
    simp only [hsucc, dite_true]
    rfl
  · right
    unfold max_with_pump_witness
    simp only [hsucc, dite_false]
    rfl

theorem matrixFunctional_with_projected_affine_pump_witness_shape
    {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixFunctionalMeasureWithProjectedAffinePump S d) :
    WitnessStepShape.Realizes
        (S := S)
        (.succPump (M.recur_counter * (M.succ_bias + M.succ_scale * M.c_base)))
        (matrixFunctional_with_projected_affine_pump_witness M).s
      ∨
      WitnessStepShape.Realizes
        (S := S)
        (.wrapPump (M.recur_counter * (M.succ_bias + M.succ_scale * M.c_base)))
        (matrixFunctional_with_projected_affine_pump_witness M).s := by
  classical
  simpa [matrixFunctional_with_projected_affine_pump_witness] using
    affine_with_pump_witness_shape (S := S) M.projectedAffineWithPump

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
