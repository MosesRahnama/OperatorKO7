import OperatorKO7.Meta.PolynomialBarrierGeneral_Schema

/-!
# WPO-Facing Polynomial-Algebra Barrier Corollary: Schema Layer

Schema-generic half of the WPO-facing direct polynomial-branch barrier.

This file packages a narrow consequence of the generalized bounded polynomial
barrier: if a direct order is sound with respect to a bounded-degree
constructor-local polynomial algebra, then that direct order already fails on
the duplicating schema step whenever the underlying polynomial barrier applies.

KO7-facing corollaries live in `Meta/WPO_PolynomialBarrier.lean`.
-/

namespace OperatorKO7.StepDuplicating.StepDuplicatingSchema

/-- Minimal WPO-facing abstraction for the direct polynomial-algebra branch.
The only assumption is that the strict comparison is sound with respect to an
already formalized bounded polynomial measure. -/
structure WPOPolynomialDirectOrder (S : StepDuplicatingSchema) where
  measure : BoundedPolynomialMeasure S
  gt : S.T → S.T → Prop
  sound : ∀ {x y : S.T}, gt x y → measure.eval y < measure.eval x

/-- Any direct WPO-style order certified by a bounded polynomial algebra inherits
the generalized polynomial barrier on the duplicating schema step. -/
theorem no_wpoPolynomialDirect_orients_dup_step_of_unbounded
    {S : StepDuplicatingSchema} (W : WPOPolynomialDirectOrder S)
    (hunbounded : HasUnboundedRangePoly W.measure)
    (hdom : EventuallyDominatedAtBase W.measure) :
    ¬ (∀ (b s n : S.T),
      W.gt (S.recur b s (S.succ n)) (S.wrap s (S.recur b s n))) := by
  intro h
  apply no_polynomial_orients_dup_step_of_unbounded (M := W.measure) hunbounded hdom
  intro b s n
  exact W.sound (h b s n)

/-- Successor-pump specialization of the WPO-facing polynomial barrier. -/
theorem no_wpoPolynomialDirect_orients_dup_step_of_succ_pump
    {S : StepDuplicatingSchema} (W : WPOPolynomialDirectOrder S)
    (h_succ_bias : 1 ≤ W.measure.succ_bias) (h_succ_scale : 1 ≤ W.measure.succ_scale)
    (hdom : EventuallyDominatedAtBase W.measure) :
    ¬ (∀ (b s n : S.T),
      W.gt (S.recur b s (S.succ n)) (S.wrap s (S.recur b s n))) := by
  intro h
  apply
    no_polynomial_orients_dup_step_of_succ_pump
      (M := W.measure) h_succ_bias h_succ_scale hdom
  intro b s n
  exact W.sound (h b s n)

/-- Wrap-pump specialization of the WPO-facing polynomial barrier. -/
theorem no_wpoPolynomialDirect_orients_dup_step_of_wrap_pump
    {S : StepDuplicatingSchema} (W : WPOPolynomialDirectOrder S)
    (h_wrap_bias : 1 ≤ W.measure.wrap_const + W.measure.wrap_right * W.measure.c_base)
    (hdom : EventuallyDominatedAtBase W.measure) :
    ¬ (∀ (b s n : S.T),
      W.gt (S.recur b s (S.succ n)) (S.wrap s (S.recur b s n))) := by
  intro h
  apply no_polynomial_orients_dup_step_of_wrap_pump (M := W.measure) h_wrap_bias hdom
  intro b s n
  exact W.sound (h b s n)

/-- Any successful direct polynomial-branch orienter must violate the same
frozen base-dominance condition as the underlying bounded polynomial measure. -/
theorem wpoPolynomialDirect_escape_requires_failure_of_base_dominance
    {S : StepDuplicatingSchema} (W : WPOPolynomialDirectOrder S)
    (hunbounded : HasUnboundedRangePoly W.measure)
    (horient : ∀ (b s n : S.T),
      W.gt (S.recur b s (S.succ n)) (S.wrap s (S.recur b s n))) :
    ¬ EventuallyDominatedAtBase W.measure := by
  apply polynomial_escape_requires_failure_of_base_dominance (M := W.measure) hunbounded
  intro b s n
  exact W.sound (horient b s n)

/-- The WPO-facing polynomial branch also fails globally on any system
containing the duplicating step. -/
theorem no_global_orients_wpoPolynomialDirect_of_unbounded
    {Sys : StepDuplicatingSystem}
    (W : WPOPolynomialDirectOrder Sys.toStepDuplicatingSchema)
    (hunbounded : HasUnboundedRangePoly W.measure)
    (hdom : EventuallyDominatedAtBase W.measure) :
    ¬ GlobalOrients Sys (fun t => t) (fun x y => W.gt y x) := by
  intro h
  apply no_wpoPolynomialDirect_orients_dup_step_of_unbounded W hunbounded hdom
  intro b s n
  exact h (Sys.dup_step b s n)

end OperatorKO7.StepDuplicating.StepDuplicatingSchema
