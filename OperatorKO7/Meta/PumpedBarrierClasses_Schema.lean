import OperatorKO7.Meta.QuadraticBarrier_Schema
import OperatorKO7.Meta.QuadraticCrossTermBarrier_Schema
import OperatorKO7.Meta.MatrixBarrierLex_Schema
import OperatorKO7.Meta.MultilinearBarrier_Schema
import OperatorKO7.Meta.PolynomialBarrierGeneral_Schema
import OperatorKO7.Meta.MaxBarrier_Schema
import OperatorKO7.Meta.MatrixBarrierFunctional_Schema
import OperatorKO7.Meta.MatrixBarrierMix2_Schema

/-!
# Pumped Barrier Classes: Schema Layer

Schema-generic half of the pumped-barrier-class development.

This file packages the growth-side hypotheses used by the affine, restricted
quadratic, multilinear, max-plus, polynomial, and tracked pair barriers into
named strengthened subclasses. The original barrier theorems remain unchanged
and conditional. The theorems here are unconditional for the strengthened
subclasses because the relevant successor- or wrapper-growth witness is built
into the class.

The KO7-specific specializations live in `Meta/PumpedBarrierClasses.lean`.
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

/-- Bounded cross-term quadratic measures with an internal successor or wrapper pump. -/
structure CrossTermQuadraticMeasureWithPump (S : StepDuplicatingSchema)
    extends CrossTermQuadraticMeasure S where
  has_pump :
    (1 ≤ succ_bias ∧ 1 ≤ succ_scale) ∨
      1 ≤ wrap_const + wrap_right * c_base
  h_bounded : CrossTermBoundedAtBase toCrossTermQuadraticMeasure

/-- Dimension-2 tracked pair measures whose primary component has an internal pump. -/
structure MatrixMeasure2WithPrimaryPump (S : StepDuplicatingSchema) extends MatrixMeasure2 S where
  has_primary_pump :
    (1 ≤ succ_bias1 ∧ 1 ≤ succ_scale1) ∨
      1 ≤ wrap_const1 + wrap_right1 * c_base1

/-- Bounded multilinear measures with an internal pump and packaged dominance witness. -/
structure MultilinearMeasureWithPump (S : StepDuplicatingSchema)
    extends BoundedMultilinearMeasure S where
  has_pump :
    (1 ≤ succ_bias ∧ 1 ≤ succ_scale) ∨
      1 ≤ wrap_const + wrap_right * c_base
  h_dominated : MultilinearDominatedAtBase toBoundedMultilinearMeasure

/-- Max-plus measures with an internal successor- or wrapper-pump witness. -/
structure MaxMeasureWithPump (S : StepDuplicatingSchema) extends MaxMeasure S where
  has_pump :
    (1 ≤ succ_const) ∨
      1 ≤ wrap_const + wrap_left

/-- Generalized bounded-polynomial measures with an internal pump and packaged frozen
base-dominance witness. -/
structure PolynomialMeasureWithPump (S : StepDuplicatingSchema)
    extends BoundedPolynomialMeasure S where
  has_pump :
    (1 ≤ succ_bias ∧ 1 ≤ succ_scale) ∨
      1 ≤ wrap_const + wrap_right * c_base
  h_dominated : EventuallyDominatedAtBase toBoundedPolynomialMeasure

/-- Weighted functional matrix measures whose chosen scalar projection has an internal
affine pump. -/
structure MatrixFunctionalMeasureWithProjectedAffinePump
    (S : StepDuplicatingSchema) (d : Nat)
    extends MatrixFunctionalMeasure S d where
  has_pump :
    (1 ≤ succ_bias ∧ 1 ≤ succ_scale) ∨
      1 ≤ wrap_const + wrap_right * c_base

/-- Balanced mixed-coordinate dimension-2 measures whose aggregate coordinate sum has an
internal affine pump. -/
structure MatrixMix2MeasureWithSumPump (S : StepDuplicatingSchema)
    extends MatrixMix2Measure S where
  has_sum_pump :
    (1 ≤ vecSum succ_bias ∧ 1 ≤ succ_mat.sumCoeff) ∨
      1 ≤ vecSum wrap_bias + wrap_right.sumCoeff * vecSum c_base

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

/-- Unconditional bounded cross-term quadratic barrier for the strengthened pumped subclass. -/
theorem no_cross_quadratic_with_pump_orients_dup_step
    {S : StepDuplicatingSchema} (M : CrossTermQuadraticMeasureWithPump S) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  rcases M.has_pump with hsucc | hwrap
  · exact
      no_cross_quadratic_orients_dup_step_of_succ_pump
        (S := S) M.toCrossTermQuadraticMeasure hsucc.1 hsucc.2 M.h_bounded
  · exact
      no_cross_quadratic_orients_dup_step_of_wrap_pump
        (S := S) M.toCrossTermQuadraticMeasure hwrap M.h_bounded

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

/-- Unconditional multilinear barrier for the strengthened pumped subclass. -/
theorem no_multilinear_with_pump_orients_dup_step
    {S : StepDuplicatingSchema} (M : MultilinearMeasureWithPump S) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  rcases M.has_pump with hsucc | hwrap
  · exact
      no_multilinear_orients_dup_step_of_succ_pump
        (S := S) M.toBoundedMultilinearMeasure hsucc.1 hsucc.2 M.h_dominated
  · exact
      no_multilinear_orients_dup_step_of_wrap_pump
        (S := S) M.toBoundedMultilinearMeasure hwrap M.h_dominated

/-- Unconditional max-plus barrier for the strengthened pumped subclass. -/
theorem no_max_with_pump_orients_dup_step
    {S : StepDuplicatingSchema} (M : MaxMeasureWithPump S) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  rcases M.has_pump with hsucc | hwrap
  · exact
      no_max_orients_dup_step_of_succ_pump
        (S := S) M.toMaxMeasure hsucc
  · exact
      no_max_orients_dup_step_of_wrap_pump
        (S := S) M.toMaxMeasure hwrap

/-- Unconditional generalized bounded-polynomial barrier for the strengthened pumped
subclass. -/
theorem no_polynomial_with_pump_orients_dup_step
    {S : StepDuplicatingSchema} (M : PolynomialMeasureWithPump S) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  rcases M.has_pump with hsucc | hwrap
  · exact
      no_polynomial_orients_dup_step_of_succ_pump
        (S := S) M.toBoundedPolynomialMeasure hsucc.1 hsucc.2 M.h_dominated
  · exact
      no_polynomial_orients_dup_step_of_wrap_pump
        (S := S) M.toBoundedPolynomialMeasure hwrap M.h_dominated

/-- The projected scalar induced by a weighted functional matrix family can itself be
packaged as an affine-with-pump measure. -/
def MatrixFunctionalMeasureWithProjectedAffinePump.projectedAffineWithPump
    {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixFunctionalMeasureWithProjectedAffinePump S d) : AffineMeasureWithPump S where
  toAffineMeasure := M.toMatrixFunctionalMeasure.projectedAffine
  has_pump := M.has_pump

/-- Unconditional weighted functional projection barrier for the strengthened pumped
subclass. -/
theorem no_matrixFunctional_with_projected_affine_pump_orients_dup_step
    {S : StepDuplicatingSchema} {d : Nat}
    (M : MatrixFunctionalMeasureWithProjectedAffinePump S d) :
    ¬ (∀ (b s n : S.T),
      VecLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  rcases M.has_pump with hsucc | hwrap
  · exact
      no_matrixFunctional_orients_dup_step_of_succ_pump
        (S := S) M.toMatrixFunctionalMeasure hsucc.1 hsucc.2
  · exact
      no_matrixFunctional_orients_dup_step_of_wrap_pump
        (S := S) M.toMatrixFunctionalMeasure hwrap

/-- The aggregate coordinate sum of a balanced mixed-coordinate family can be packaged as
an affine-with-pump measure. -/
def MatrixMix2MeasureWithSumPump.sumAffineWithPump
    {S : StepDuplicatingSchema} (M : MatrixMix2MeasureWithSumPump S) : AffineMeasureWithPump S where
  toAffineMeasure := M.toMatrixMix2Measure.sumAffine
  has_pump := M.has_sum_pump

/-- Unconditional balanced mixed-coordinate barrier for the strengthened pumped subclass. -/
theorem no_matrixMix2_with_sum_pump_orients_dup_step
    {S : StepDuplicatingSchema} (M : MatrixMix2MeasureWithSumPump S) :
    ¬ (∀ (b s n : S.T),
      PairLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  have hsum :
      ∀ (b s n : S.T),
        vecSum (M.eval (S.wrap s (S.recur b s n))) <
          vecSum (M.eval (S.recur b s (S.succ n))) := by
    intro b s n
    exact vecSum_lt_of_pairLt (h b s n)
  exact
    no_affine_with_pump_orients_dup_step
      (S := S) M.sumAffineWithPump hsum

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

/-- The strengthened pumped bounded cross-term subclass also fails globally. -/
theorem no_global_orients_cross_quadratic_with_pump
    {Sys : StepDuplicatingSystem}
    (M : CrossTermQuadraticMeasureWithPump Sys.toStepDuplicatingSchema) :
    ¬ GlobalOrients Sys M.eval (· < ·) := by
  rcases M.has_pump with hsucc | hwrap
  · exact
      no_global_orients_cross_quadratic_of_succ_pump
        (Sys := Sys) M.toCrossTermQuadraticMeasure hsucc.1 hsucc.2 M.h_bounded
  · exact
      no_global_orients_cross_quadratic_of_wrap_pump
        (Sys := Sys) M.toCrossTermQuadraticMeasure hwrap M.h_bounded

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

/-- The strengthened multilinear subclass also fails globally. -/
theorem no_global_orients_multilinear_with_pump
    {Sys : StepDuplicatingSystem}
    (M : MultilinearMeasureWithPump Sys.toStepDuplicatingSchema) :
    ¬ GlobalOrients Sys M.eval (· < ·) := by
  rcases M.has_pump with hsucc | hwrap
  · exact
      no_global_orients_multilinear_of_succ_pump
        (Sys := Sys) M.toBoundedMultilinearMeasure hsucc.1 hsucc.2 M.h_dominated
  · exact
      no_global_orients_multilinear_of_wrap_pump
        (Sys := Sys) M.toBoundedMultilinearMeasure hwrap M.h_dominated

/-- The strengthened max-plus subclass also fails globally. -/
theorem no_global_orients_max_with_pump
    {Sys : StepDuplicatingSystem}
    (M : MaxMeasureWithPump Sys.toStepDuplicatingSchema) :
    ¬ GlobalOrients Sys M.eval (· < ·) := by
  rcases M.has_pump with hsucc | hwrap
  · exact
      no_global_orients_max_of_unbounded
        (Sys := Sys) M.toMaxMeasure
        (fun k => by
          refine ⟨succIter Sys.toStepDuplicatingSchema k, ?_⟩
          simpa using eval_succIter_ge_max (M := M.toMaxMeasure) hsucc k)
  · exact
      no_global_orients_max_of_unbounded
        (Sys := Sys) M.toMaxMeasure
        (fun k => by
          refine ⟨wrapIter Sys.toStepDuplicatingSchema k, ?_⟩
          simpa using eval_wrapIter_ge_max (M := M.toMaxMeasure) hwrap k)

/-- The strengthened generalized bounded-polynomial subclass also fails globally. -/
theorem no_global_orients_polynomial_with_pump
    {Sys : StepDuplicatingSystem}
    (M : PolynomialMeasureWithPump Sys.toStepDuplicatingSchema) :
    ¬ GlobalOrients Sys M.eval (· < ·) := by
  rcases M.has_pump with hsucc | hwrap
  · exact
      (fun h =>
        StepDuplicatingSchema.no_polynomial_orients_dup_step_of_succ_pump
          (S := Sys.toStepDuplicatingSchema) M.toBoundedPolynomialMeasure
          hsucc.1 hsucc.2 M.h_dominated
          (fun b s n => h (Sys.dup_step b s n)))
  · exact
      (fun h =>
        StepDuplicatingSchema.no_polynomial_orients_dup_step_of_wrap_pump
          (S := Sys.toStepDuplicatingSchema) M.toBoundedPolynomialMeasure
          hwrap M.h_dominated
          (fun b s n => h (Sys.dup_step b s n)))

/-- The strengthened weighted functional projection subclass also fails globally. -/
theorem no_global_orients_matrixFunctional_with_projected_affine_pump
    {Sys : StepDuplicatingSystem} {d : Nat}
    (M : MatrixFunctionalMeasureWithProjectedAffinePump Sys.toStepDuplicatingSchema d) :
    ¬ GlobalOrients Sys M.eval VecLt := by
  intro h
  exact
    no_matrixFunctional_with_projected_affine_pump_orients_dup_step
      (S := Sys.toStepDuplicatingSchema) M
      (fun b s n => h (Sys.dup_step b s n))

/-- The strengthened balanced mixed-coordinate subclass also fails globally. -/
theorem no_global_orients_matrixMix2_with_sum_pump
    {Sys : StepDuplicatingSystem}
    (M : MatrixMix2MeasureWithSumPump Sys.toStepDuplicatingSchema) :
    ¬ GlobalOrients Sys M.eval PairLt := by
  intro h
  exact
    no_matrixMix2_with_sum_pump_orients_dup_step
      (S := Sys.toStepDuplicatingSchema) M
      (fun b s n => h (Sys.dup_step b s n))

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
