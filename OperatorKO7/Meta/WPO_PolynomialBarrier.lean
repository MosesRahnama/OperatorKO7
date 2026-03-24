import OperatorKO7.Meta.PolynomialBarrierGeneral

/-!
# WPO-Facing Polynomial-Algebra Barrier Corollary

This module does **not** formalize generic weighted path order metatheory.
Instead, it packages a narrow consequence of the existing generalized bounded
polynomial barrier:

- if a direct order certifies strict comparison by a bounded-degree
  constructor-local polynomial algebra, then the polynomial barrier already
  blocks that direct order on the duplicating schema step.

This is intended as a WPO-facing corollary for the direct polynomial-algebra
branch used in tool implementations, not as a theorem about recursive path
descent, max branches, or full WPO completeness.
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

namespace OperatorKO7.WPOPolynomialBarrier

open OperatorKO7
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

/-- KO7-facing WPO polynomial-branch corollary under an unbounded direct algebra. -/
theorem no_global_step_orientation_wpoPolynomialDirect_of_unbounded
    (W : StepDuplicatingSchema.WPOPolynomialDirectOrder ko7Schema)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRangePoly W.measure)
    (hdom : StepDuplicatingSchema.EventuallyDominatedAtBase W.measure) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System (fun t => t) (fun x y => W.gt y x) := by
  exact
    StepDuplicatingSchema.no_global_orients_wpoPolynomialDirect_of_unbounded
      (Sys := ko7System) W hunbounded hdom

/-- KO7 successor-pump specialization for the direct polynomial branch. -/
theorem no_global_step_orientation_wpoPolynomialDirect_of_succ_pump
    (W : StepDuplicatingSchema.WPOPolynomialDirectOrder ko7Schema)
    (h_succ_bias : 1 ≤ W.measure.succ_bias) (h_succ_scale : 1 ≤ W.measure.succ_scale)
    (hdom : StepDuplicatingSchema.EventuallyDominatedAtBase W.measure) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System (fun t => t) (fun x y => W.gt y x) := by
  intro h
  apply
    StepDuplicatingSchema.no_wpoPolynomialDirect_orients_dup_step_of_succ_pump
      (W := W) h_succ_bias h_succ_scale hdom
  intro b s n
  exact h (ko7System.dup_step b s n)

/-- KO7 wrap-pump specialization for the direct polynomial branch. -/
theorem no_global_step_orientation_wpoPolynomialDirect_of_wrap_pump
    (W : StepDuplicatingSchema.WPOPolynomialDirectOrder ko7Schema)
    (h_wrap_bias : 1 ≤ W.measure.wrap_const + W.measure.wrap_right * W.measure.c_base)
    (hdom : StepDuplicatingSchema.EventuallyDominatedAtBase W.measure) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System (fun t => t) (fun x y => W.gt y x) := by
  intro h
  apply
    StepDuplicatingSchema.no_wpoPolynomialDirect_orients_dup_step_of_wrap_pump
      (W := W) h_wrap_bias hdom
  intro b s n
  exact h (ko7System.dup_step b s n)

/-- KO7-facing necessary condition for any successful direct WPO-style escape
through a bounded polynomial algebra branch. -/
theorem wpoPolynomialDirect_escape_requires_failure_of_base_dominance
    (W : StepDuplicatingSchema.WPOPolynomialDirectOrder ko7Schema)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRangePoly W.measure)
    (horient : StepDuplicatingSchema.GlobalOrients ko7System (fun t => t) (fun x y => W.gt y x)) :
    ¬ StepDuplicatingSchema.EventuallyDominatedAtBase W.measure := by
  apply
    StepDuplicatingSchema.wpoPolynomialDirect_escape_requires_failure_of_base_dominance
      (W := W) hunbounded
  intro b s n
  exact horient (ko7System.dup_step b s n)

end OperatorKO7.WPOPolynomialBarrier
