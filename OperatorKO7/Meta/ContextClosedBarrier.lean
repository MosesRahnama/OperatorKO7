import OperatorKO7.Meta.CompositionalMeasure_Impossibility
import OperatorKO7.Meta.PumpedBarrierClasses
import OperatorKO7.Meta.ContextClosed_SN_Full

/-!
# Context-Closed Barrier Survival

The direct barrier stack is proved against the root duplicating step. Since every
root step embeds into the full context closure `StepCtxFull` via the identity
context, any putative orienter of `StepCtxFull` would in particular orient the
root duplicating step. This file records that bridge explicitly.
-/

namespace OperatorKO7.ContextClosedBarrier

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.PumpedBarrierClasses
open MetaSN_KO7

/-- Global orientation of the full context-closed relation `StepCtxFull`. -/
def GlobalOrientsStepCtxFull {α : Type} (m : Trace → α) (lt : α → α → Prop) : Prop :=
  ∀ {a b : Trace}, StepCtxFull a b → lt (m b) (m a)

/-- Any orienter of `StepCtxFull` also orients the root relation `Step`. -/
theorem stepCtxFull_orientation_implies_root
    {α : Type} {m : Trace → α} {lt : α → α → Prop}
    (h : GlobalOrientsStepCtxFull m lt) :
    StepDuplicatingSchema.GlobalOrients ko7System m lt := by
  intro a b hab
  exact h (StepCtxFull.root hab)

/-- Additive compositional barriers survive to the full context closure. -/
theorem no_stepCtxFull_orientation_additive_compositional
    (M : AdditiveCompositionalMeasure) :
    ¬ GlobalOrientsStepCtxFull M.eval (· < ·) := by
  intro h
  exact
    no_global_step_orientation_additive_compositional M
      (stepCtxFull_orientation_implies_root h)

/-- Transparent-compositional barriers survive to the full context closure. -/
theorem no_stepCtxFull_orientation_compositional_transparent_delta
    (CM : CompositionalMeasure)
    (htrans : CM.c_delta CM.c_void = CM.c_void) :
    ¬ GlobalOrientsStepCtxFull CM.eval (· < ·) := by
  intro h
  exact
    no_global_step_orientation_compositional_transparent_delta CM htrans
      (stepCtxFull_orientation_implies_root h)

/-- Affine-with-pump barriers survive to the full context closure. -/
theorem no_stepCtxFull_orientation_affine_with_pump
    (M : StepDuplicatingSchema.AffineMeasureWithPump ko7Schema) :
    ¬ GlobalOrientsStepCtxFull M.eval (· < ·) := by
  intro h
  exact
    no_global_step_orientation_affine_with_pump M
      (stepCtxFull_orientation_implies_root h)

/-- Restricted quadratic-with-pump barriers survive to the full context closure. -/
theorem no_stepCtxFull_orientation_quadratic_with_pump
    (M : StepDuplicatingSchema.QuadraticCounterMeasureWithPump ko7Schema) :
    ¬ GlobalOrientsStepCtxFull M.eval (· < ·) := by
  intro h
  exact
    no_global_step_orientation_quadratic_with_pump M
      (stepCtxFull_orientation_implies_root h)

/-- Bounded cross-quadratic-with-pump barriers survive to the full context closure. -/
theorem no_stepCtxFull_orientation_cross_quadratic_with_pump
    (M : StepDuplicatingSchema.CrossTermQuadraticMeasureWithPump ko7Schema) :
    ¬ GlobalOrientsStepCtxFull M.eval (· < ·) := by
  intro h
  exact
    no_global_step_orientation_cross_quadratic_with_pump M
      (stepCtxFull_orientation_implies_root h)

/-- Tracked-primary componentwise pair barriers survive to the full context closure. -/
theorem no_stepCtxFull_orientation_matrix2_with_primary_pump
    (M : StepDuplicatingSchema.MatrixMeasure2WithPrimaryPump ko7Schema) :
    ¬ GlobalOrientsStepCtxFull M.eval StepDuplicatingSchema.PairLt := by
  intro h
  exact
    no_global_step_orientation_matrix2_with_primary_pump M
      (stepCtxFull_orientation_implies_root h)

/-- Tracked-primary lexicographic pair barriers survive to the full context closure. -/
theorem no_stepCtxFull_orientation_matrix2_lex_with_primary_pump
    (M : StepDuplicatingSchema.MatrixMeasure2WithPrimaryPump ko7Schema) :
    ¬ GlobalOrientsStepCtxFull M.eval StepDuplicatingSchema.PairLexLt := by
  intro h
  exact
    no_global_step_orientation_matrix2_lex_with_primary_pump M
      (stepCtxFull_orientation_implies_root h)

/-- Multilinear-with-pump barriers survive to the full context closure. -/
theorem no_stepCtxFull_orientation_multilinear_with_pump
    (M : StepDuplicatingSchema.MultilinearMeasureWithPump ko7Schema) :
    ¬ GlobalOrientsStepCtxFull M.eval (· < ·) := by
  intro h
  exact
    no_global_step_orientation_multilinear_with_pump M
      (stepCtxFull_orientation_implies_root h)

/-- Max-with-pump barriers survive to the full context closure. -/
theorem no_stepCtxFull_orientation_max_with_pump
    (M : StepDuplicatingSchema.MaxMeasureWithPump ko7Schema) :
    ¬ GlobalOrientsStepCtxFull M.eval (· < ·) := by
  intro h
  exact
    no_global_step_orientation_max_with_pump M
      (stepCtxFull_orientation_implies_root h)

/-- Weighted scalar-projection barriers survive to the full context closure. -/
theorem no_stepCtxFull_orientation_matrixFunctional_with_projected_affine_pump
    {d : Nat}
    (M : StepDuplicatingSchema.MatrixFunctionalMeasureWithProjectedAffinePump ko7Schema d) :
    ¬ GlobalOrientsStepCtxFull M.eval StepDuplicatingSchema.VecLt := by
  intro h
  exact
    no_global_step_orientation_matrixFunctional_with_projected_affine_pump M
      (stepCtxFull_orientation_implies_root h)

/-- Balanced mixed-coordinate barriers survive to the full context closure. -/
theorem no_stepCtxFull_orientation_matrixMix2_with_sum_pump
    (M : StepDuplicatingSchema.MatrixMix2MeasureWithSumPump ko7Schema) :
    ¬ GlobalOrientsStepCtxFull M.eval StepDuplicatingSchema.PairLt := by
  intro h
  exact
    no_global_step_orientation_matrixMix2_with_sum_pump M
      (stepCtxFull_orientation_implies_root h)

end OperatorKO7.ContextClosedBarrier
