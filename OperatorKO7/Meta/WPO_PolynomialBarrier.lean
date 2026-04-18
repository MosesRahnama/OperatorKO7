import OperatorKO7.Meta.WPO_PolynomialBarrier_Schema
import OperatorKO7.Meta.CompositionalMeasure_Impossibility

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
