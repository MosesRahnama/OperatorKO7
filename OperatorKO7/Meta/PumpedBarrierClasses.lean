import OperatorKO7.Meta.QuadraticBarrier
import OperatorKO7.Meta.MatrixBarrierLex

/-!
# Pumped Barrier Classes

This module packages the growth-side hypotheses used by the affine, restricted quadratic,
and tracked pair barriers into named strengthened subclasses. The original barrier theorems
remain unchanged and conditional. The theorems here are unconditional for the strengthened
subclasses because the relevant successor- or wrapper-growth witness is built into the class.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-- Affine constructor-local measures with an internal successor or wrapper pump. -/
structure AffineMeasureWithPump (S : StepDuplicatingSchema) extends AffineMeasure S where
  has_pump :
    (1 ≤ succ_bias ∧ 1 ≤ succ_scale) ∨
      1 ≤ wrap_const + wrap_right * c_base

/-- Restricted quadratic counter measures with an internal successor or wrapper pump. -/
structure QuadraticCounterMeasureWithPump (S : StepDuplicatingSchema)
    extends QuadraticCounterMeasure S where
  has_pump :
    (1 ≤ succ_bias ∧ 1 ≤ succ_scale) ∨
      1 ≤ wrap_const + wrap_right * c_base

/-- Dimension-2 tracked pair measures whose primary component has an internal pump. -/
structure MatrixMeasure2WithPrimaryPump (S : StepDuplicatingSchema) extends MatrixMeasure2 S where
  has_primary_pump :
    (1 ≤ succ_bias1 ∧ 1 ≤ succ_scale1) ∨
      1 ≤ wrap_const1 + wrap_right1 * c_base1

/-- Unconditional affine barrier for the strengthened pumped subclass. -/
theorem no_affine_with_pump_orients_dup_step
    {S : StepDuplicatingSchema} (M : AffineMeasureWithPump S) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  rcases M.has_pump with hsucc | hwrap
  · exact
      no_affine_orients_dup_step_of_succ_pump
        (S := S) M.toAffineMeasure hsucc.1 hsucc.2
  · exact
      no_affine_orients_dup_step_of_wrap_pump
        (S := S) M.toAffineMeasure hwrap

/-- Unconditional restricted quadratic barrier for the strengthened pumped subclass. -/
theorem no_quadratic_with_pump_orients_dup_step
    {S : StepDuplicatingSchema} (M : QuadraticCounterMeasureWithPump S) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  rcases M.has_pump with hsucc | hwrap
  · exact
      no_quadratic_counter_orients_dup_step_of_succ_pump
        (S := S) M.toQuadraticCounterMeasure hsucc.1 hsucc.2
  · exact
      no_quadratic_counter_orients_dup_step_of_wrap_pump
        (S := S) M.toQuadraticCounterMeasure hwrap

/-- Unconditional componentwise pair barrier for the strengthened tracked-primary subclass. -/
theorem no_matrix2_with_primary_pump_componentwise_orients_dup_step
    {S : StepDuplicatingSchema} (M : MatrixMeasure2WithPrimaryPump S) :
    ¬ (∀ (b s n : S.T),
      PairLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  rcases M.has_primary_pump with hsucc | hwrap
  · exact
      no_matrix2_orients_dup_step_of_succ_pump
        (S := S) M.toMatrixMeasure2 hsucc.1 hsucc.2
  · exact
      no_matrix2_orients_dup_step_of_wrap_pump
        (S := S) M.toMatrixMeasure2 hwrap

/-- Unconditional lexicographic pair barrier for the strengthened tracked-primary subclass. -/
theorem no_matrix2_with_primary_pump_lex_orients_dup_step
    {S : StepDuplicatingSchema} (M : MatrixMeasure2WithPrimaryPump S) :
    ¬ (∀ (b s n : S.T),
      PairLexLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  rcases M.has_primary_pump with hsucc | hwrap
  · exact
      no_matrix2_lex_orients_dup_step_of_succ_pump
        (S := S) M.toMatrixMeasure2 hsucc.1 hsucc.2
  · exact
      no_matrix2_lex_orients_dup_step_of_wrap_pump
        (S := S) M.toMatrixMeasure2 hwrap

/-- Any globally oriented system containing the duplicating step would orient that step.
The strengthened pumped affine subclass therefore also fails globally. -/
theorem no_global_orients_affine_with_pump
    {Sys : StepDuplicatingSystem}
    (M : AffineMeasureWithPump Sys.toStepDuplicatingSchema) :
    ¬ GlobalOrients Sys M.eval (· < ·) := by
  rcases M.has_pump with hsucc | hwrap
  · exact
      no_global_orients_affine_of_succ_pump
        (Sys := Sys) M.toAffineMeasure hsucc.1 hsucc.2
  · exact
      no_global_orients_affine_of_wrap_pump
        (Sys := Sys) M.toAffineMeasure hwrap

/-- The strengthened pumped restricted quadratic subclass also fails globally. -/
theorem no_global_orients_quadratic_with_pump
    {Sys : StepDuplicatingSystem}
    (M : QuadraticCounterMeasureWithPump Sys.toStepDuplicatingSchema) :
    ¬ GlobalOrients Sys M.eval (· < ·) := by
  rcases M.has_pump with hsucc | hwrap
  · exact
      no_global_orients_quadratic_of_succ_pump
        (Sys := Sys) M.toQuadraticCounterMeasure hsucc.1 hsucc.2
  · exact
      no_global_orients_quadratic_of_wrap_pump
        (Sys := Sys) M.toQuadraticCounterMeasure hwrap

/-- The strengthened tracked-primary componentwise pair subclass also fails globally. -/
theorem no_global_orients_matrix2_with_primary_pump
    {Sys : StepDuplicatingSystem}
    (M : MatrixMeasure2WithPrimaryPump Sys.toStepDuplicatingSchema) :
    ¬ GlobalOrients Sys M.eval PairLt := by
  rcases M.has_primary_pump with hsucc | hwrap
  · intro h
    have hdup :
        ∀ b s n : Sys.T,
          PairLt (M.eval (Sys.wrap s (Sys.recur b s n)))
            (M.eval (Sys.recur b s (Sys.succ n))) := by
      intro b s n
      exact h (Sys.dup_step b s n)
    exact
      no_matrix2_orients_dup_step_of_succ_pump
        (S := Sys.toStepDuplicatingSchema) M.toMatrixMeasure2 hsucc.1 hsucc.2 hdup
  · intro h
    have hdup :
        ∀ b s n : Sys.T,
          PairLt (M.eval (Sys.wrap s (Sys.recur b s n)))
            (M.eval (Sys.recur b s (Sys.succ n))) := by
      intro b s n
      exact h (Sys.dup_step b s n)
    exact
      no_matrix2_orients_dup_step_of_wrap_pump
        (S := Sys.toStepDuplicatingSchema) M.toMatrixMeasure2 hwrap hdup

/-- The strengthened tracked-primary lexicographic pair subclass also fails globally. -/
theorem no_global_orients_matrix2_lex_with_primary_pump
    {Sys : StepDuplicatingSystem}
    (M : MatrixMeasure2WithPrimaryPump Sys.toStepDuplicatingSchema) :
    ¬ GlobalOrients Sys M.eval PairLexLt := by
  rcases M.has_primary_pump with hsucc | hwrap
  · intro h
    have hdup :
        ∀ b s n : Sys.T,
          PairLexLt (M.eval (Sys.wrap s (Sys.recur b s n)))
            (M.eval (Sys.recur b s (Sys.succ n))) := by
      intro b s n
      exact h (Sys.dup_step b s n)
    exact
      no_matrix2_lex_orients_dup_step_of_succ_pump
        (S := Sys.toStepDuplicatingSchema) M.toMatrixMeasure2 hsucc.1 hsucc.2 hdup
  · intro h
    have hdup :
        ∀ b s n : Sys.T,
          PairLexLt (M.eval (Sys.wrap s (Sys.recur b s n)))
            (M.eval (Sys.recur b s (Sys.succ n))) := by
      intro b s n
      exact h (Sys.dup_step b s n)
    exact
      no_matrix2_lex_orients_dup_step_of_wrap_pump
        (S := Sys.toStepDuplicatingSchema) M.toMatrixMeasure2 hwrap hdup

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating

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

end OperatorKO7.PumpedBarrierClasses
