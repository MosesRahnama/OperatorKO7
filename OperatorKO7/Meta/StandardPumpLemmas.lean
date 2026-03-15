import OperatorKO7.Meta.PumpedBarrierClasses

/-!
# Standard Pump Lemmas

This module factors out the growth lemmas that connect the current conditional barrier
theorems to the explicit positive-growth subclasses already formalized in the artifact.

Why this file exists:
- Exposes reusable unboundedness lemmas for the current affine, restricted-quadratic,
  and tracked-primary pair families.
- Packages the corresponding positive-growth hypotheses into the pumped subclasses as
  explicit constructors, rather than leaving that bridge implicit in barrier corollaries.
- Keeps the scope honest: this is a bridge for the standard constructor-local families
  already formalized here, not a theorem about every external tool format or heuristic.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-- Positive affine successor drift yields an explicit unbounded-range witness. -/
theorem affine_hasUnboundedRange_of_succ_pump
    {S : StepDuplicatingSchema} (M : AffineMeasure S)
    (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale) :
    HasUnboundedRange M := by
  intro k
  refine ⟨succIter S k, ?_⟩
  simpa using eval_succIter_ge M h_succ_bias h_succ_scale k

/-- Positive affine wrap/base drift yields an explicit unbounded-range witness. -/
theorem affine_hasUnboundedRange_of_wrap_pump
    {S : StepDuplicatingSchema} (M : AffineMeasure S)
    (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base) :
    HasUnboundedRange M := by
  intro k
  refine ⟨wrapIter S k, ?_⟩
  simpa using eval_wrapIter_ge_affine M h_wrap_bias k

/-- Promote an affine measure with positive successor drift to the pumped subclass. -/
def AffineMeasure.withSuccPump {S : StepDuplicatingSchema}
    (M : AffineMeasure S)
    (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale) :
    AffineMeasureWithPump S where
  toAffineMeasure := M
  has_pump := Or.inl ⟨h_succ_bias, h_succ_scale⟩

/-- Promote an affine measure with positive wrap/base drift to the pumped subclass. -/
def AffineMeasure.withWrapPump {S : StepDuplicatingSchema}
    (M : AffineMeasure S)
    (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base) :
    AffineMeasureWithPump S where
  toAffineMeasure := M
  has_pump := Or.inr h_wrap_bias

/-- Positive restricted-quadratic successor drift yields explicit unbounded range. -/
theorem quadratic_hasUnboundedRange_of_succ_pump
    {S : StepDuplicatingSchema} (M : QuadraticCounterMeasure S)
    (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale) :
    HasUnboundedRangeQ M := by
  intro k
  refine ⟨succIter S k, ?_⟩
  simpa using eval_succIter_ge_quadratic (M := M) h_succ_bias h_succ_scale k

/-- Positive restricted-quadratic wrap/base drift yields explicit unbounded range. -/
theorem quadratic_hasUnboundedRange_of_wrap_pump
    {S : StepDuplicatingSchema} (M : QuadraticCounterMeasure S)
    (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base) :
    HasUnboundedRangeQ M := by
  intro k
  refine ⟨wrapIter S k, ?_⟩
  simpa using eval_wrapIter_ge_quadratic (M := M) h_wrap_bias k

/-- Promote a restricted-quadratic measure with successor drift to the pumped subclass. -/
def QuadraticCounterMeasure.withSuccPump {S : StepDuplicatingSchema}
    (M : QuadraticCounterMeasure S)
    (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale) :
    QuadraticCounterMeasureWithPump S where
  toQuadraticCounterMeasure := M
  has_pump := Or.inl ⟨h_succ_bias, h_succ_scale⟩

/-- Promote a restricted-quadratic measure with wrap/base drift to the pumped subclass. -/
def QuadraticCounterMeasure.withWrapPump {S : StepDuplicatingSchema}
    (M : QuadraticCounterMeasure S)
    (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base) :
    QuadraticCounterMeasureWithPump S where
  toQuadraticCounterMeasure := M
  has_pump := Or.inr h_wrap_bias

/-- Positive successor drift in the tracked first component yields explicit unbounded range. -/
theorem matrix2_hasUnboundedRange1_of_succ_pump
    {S : StepDuplicatingSchema} (M : MatrixMeasure2 S)
    (h_succ_bias : 1 ≤ M.succ_bias1) (h_succ_scale : 1 ≤ M.succ_scale1) :
    HasUnboundedRange1 M := by
  intro k
  refine ⟨succIter S k, ?_⟩
  simpa using eval_succIter_ge M.fstAffine h_succ_bias h_succ_scale k

/-- Positive wrap/base drift in the tracked first component yields explicit unbounded range. -/
theorem matrix2_hasUnboundedRange1_of_wrap_pump
    {S : StepDuplicatingSchema} (M : MatrixMeasure2 S)
    (h_wrap_bias : 1 ≤ M.wrap_const1 + M.wrap_right1 * M.c_base1) :
    HasUnboundedRange1 M := by
  intro k
  refine ⟨wrapIter S k, ?_⟩
  simpa using eval_wrapIter_ge_affine M.fstAffine h_wrap_bias k

/-- Promote a tracked-primary pair measure with successor drift to the pumped subclass. -/
def MatrixMeasure2.withPrimarySuccPump {S : StepDuplicatingSchema}
    (M : MatrixMeasure2 S)
    (h_succ_bias : 1 ≤ M.succ_bias1) (h_succ_scale : 1 ≤ M.succ_scale1) :
    MatrixMeasure2WithPrimaryPump S where
  toMatrixMeasure2 := M
  has_primary_pump := Or.inl ⟨h_succ_bias, h_succ_scale⟩

/-- Promote a tracked-primary pair measure with wrap/base drift to the pumped subclass. -/
def MatrixMeasure2.withPrimaryWrapPump {S : StepDuplicatingSchema}
    (M : MatrixMeasure2 S)
    (h_wrap_bias : 1 ≤ M.wrap_const1 + M.wrap_right1 * M.c_base1) :
    MatrixMeasure2WithPrimaryPump S where
  toMatrixMeasure2 := M
  has_primary_pump := Or.inr h_wrap_bias

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
