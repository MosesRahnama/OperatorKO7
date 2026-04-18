import OperatorKO7.Meta.PumpedBarrierClasses_Schema
import OperatorKO7.Meta.CompositionalMeasure_Impossibility

/-!
# Pumped Barrier Classes

This module packages the growth-side hypotheses used by the affine, restricted quadratic,
and tracked pair barriers into named strengthened subclasses. The original barrier theorems
remain unchanged and conditional. The theorems here are unconditional for the strengthened
subclasses because the relevant successor- or wrapper-growth witness is built into the class.
-/

namespace OperatorKO7.PumpedBarrierClasses

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

/-- KO7 affine-with-pump specialization. -/
theorem no_global_step_orientation_affine_with_pump
    (M : StepDuplicatingSchema.AffineMeasureWithPump ko7Schema) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval (· < ·) := by
  exact
    StepDuplicatingSchema.no_global_orients_affine_with_pump
      (Sys := ko7System) M

/-- KO7 restricted-quadratic-with-pump specialization. -/
theorem no_global_step_orientation_quadratic_with_pump
    (M : StepDuplicatingSchema.QuadraticCounterMeasureWithPump ko7Schema) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval (· < ·) := by
  exact
    StepDuplicatingSchema.no_global_orients_quadratic_with_pump
      (Sys := ko7System) M

/-- KO7 bounded-cross-term-with-pump specialization. -/
theorem no_global_step_orientation_cross_quadratic_with_pump
    (M : StepDuplicatingSchema.CrossTermQuadraticMeasureWithPump ko7Schema) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval (· < ·) := by
  exact
    StepDuplicatingSchema.no_global_orients_cross_quadratic_with_pump
      (Sys := ko7System) M

/-- KO7 tracked-primary componentwise pair specialization. -/
theorem no_global_step_orientation_matrix2_with_primary_pump
    (M : StepDuplicatingSchema.MatrixMeasure2WithPrimaryPump ko7Schema) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval StepDuplicatingSchema.PairLt := by
  exact
    StepDuplicatingSchema.no_global_orients_matrix2_with_primary_pump
      (Sys := ko7System) M

/-- KO7 tracked-primary lexicographic pair specialization. -/
theorem no_global_step_orientation_matrix2_lex_with_primary_pump
    (M : StepDuplicatingSchema.MatrixMeasure2WithPrimaryPump ko7Schema) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval StepDuplicatingSchema.PairLexLt := by
  exact
    StepDuplicatingSchema.no_global_orients_matrix2_lex_with_primary_pump
      (Sys := ko7System) M

/-- KO7 multilinear-with-pump specialization. -/
theorem no_global_step_orientation_multilinear_with_pump
    (M : StepDuplicatingSchema.MultilinearMeasureWithPump ko7Schema) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval (· < ·) := by
  exact
    StepDuplicatingSchema.no_global_orients_multilinear_with_pump
      (Sys := ko7System) M

/-- KO7 max-plus-with-pump specialization. -/
theorem no_global_step_orientation_max_with_pump
    (M : StepDuplicatingSchema.MaxMeasureWithPump ko7Schema) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval (· < ·) := by
  exact
    StepDuplicatingSchema.no_global_orients_max_with_pump
      (Sys := ko7System) M

/-- KO7 generalized-bounded-polynomial-with-pump specialization. -/
theorem no_global_step_orientation_polynomial_with_pump
    (M : StepDuplicatingSchema.PolynomialMeasureWithPump ko7Schema) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval (· < ·) := by
  exact
    StepDuplicatingSchema.no_global_orients_polynomial_with_pump
      (Sys := ko7System) M

/-- KO7 weighted functional projected-affine pumped specialization. -/
theorem no_global_step_orientation_matrixFunctional_with_projected_affine_pump
    {d : Nat} (M : StepDuplicatingSchema.MatrixFunctionalMeasureWithProjectedAffinePump ko7Schema d) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval StepDuplicatingSchema.VecLt := by
  exact
    StepDuplicatingSchema.no_global_orients_matrixFunctional_with_projected_affine_pump
      (Sys := ko7System) M

/-- KO7 balanced mixed-coordinate sum-pumped specialization. -/
theorem no_global_step_orientation_matrixMix2_with_sum_pump
    (M : StepDuplicatingSchema.MatrixMix2MeasureWithSumPump ko7Schema) :
    ¬ StepDuplicatingSchema.GlobalOrients ko7System M.eval StepDuplicatingSchema.PairLt := by
  exact
    StepDuplicatingSchema.no_global_orients_matrixMix2_with_sum_pump
      (Sys := ko7System) M

end OperatorKO7.PumpedBarrierClasses
