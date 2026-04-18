import OperatorKO7.Meta.PolynomialBarrierGeneral_Schema
import OperatorKO7.Meta.CompositionalMeasure_Impossibility

namespace OperatorKO7.PolynomialBarrierGeneral

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

/-- KO7 specialization of the generalized degree-bounded polynomial barrier. -/
theorem no_global_step_orientation_polynomial_of_unbounded
    (M : StepDuplicatingSchema.BoundedPolynomialMeasure ko7Schema)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRangePoly M)
    (hdom : StepDuplicatingSchema.EventuallyDominatedAtBase M) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval (· < ·) := by
  exact
    StepDuplicatingSchema.no_global_orients_polynomial_of_unbounded
      (Sys := ko7System) M hunbounded hdom

/-- KO7 successor-pump specialization of the generalized polynomial barrier. -/
theorem no_global_step_orientation_polynomial_of_succ_pump
    (M : StepDuplicatingSchema.BoundedPolynomialMeasure ko7Schema)
    (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale)
    (hdom : StepDuplicatingSchema.EventuallyDominatedAtBase M) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval (· < ·) := by
  intro h
  exact
    StepDuplicatingSchema.no_polynomial_orients_dup_step_of_succ_pump
      (S := ko7Schema) M h_succ_bias h_succ_scale hdom
      (fun b s n => h (ko7System.dup_step b s n))

/-- KO7 wrap-pump specialization of the generalized polynomial barrier. -/
theorem no_global_step_orientation_polynomial_of_wrap_pump
    (M : StepDuplicatingSchema.BoundedPolynomialMeasure ko7Schema)
    (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base)
    (hdom : StepDuplicatingSchema.EventuallyDominatedAtBase M) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval (· < ·) := by
  intro h
  exact
    StepDuplicatingSchema.no_polynomial_orients_dup_step_of_wrap_pump
      (S := ko7Schema) M h_wrap_bias hdom
      (fun b s n => h (ko7System.dup_step b s n))

/-- KO7-facing necessary condition for any successful generalized polynomial escape. -/
theorem polynomial_escape_requires_failure_of_base_dominance
    (M : StepDuplicatingSchema.BoundedPolynomialMeasure ko7Schema)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRangePoly M)
    (horient : StepDuplicatingSchema.GlobalOrients ko7System M.eval (· < ·)) :
    ¬ StepDuplicatingSchema.EventuallyDominatedAtBase M := by
  apply StepDuplicatingSchema.polynomial_escape_requires_failure_of_base_dominance
    (S := ko7Schema) M hunbounded
  intro b s n
  exact horient (ko7System.dup_step b s n)

end OperatorKO7.PolynomialBarrierGeneral
