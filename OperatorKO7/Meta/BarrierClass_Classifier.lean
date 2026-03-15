import OperatorKO7.Meta.QuadraticBarrier
import OperatorKO7.Meta.MatrixBarrierLex
import OperatorKO7.Meta.QuadraticCrossTermBarrier

/-!
# Coefficient-Table Classifier for Barrier Families

This module provides a small decidable classifier for the coefficient-based barrier families.
It is intentionally syntactic: given a normalized coefficient table, it reports which
formalized coefficient families the table inhabits and which standard coefficient-side pump
conditions are visible directly from the coefficients.

The goal is not to parse arbitrary polynomial syntax. The goal is to close the loop between
an explicit coefficient table and the barrier theorems that are structurally relevant to it.
-/

namespace OperatorKO7.StepDuplicating
namespace StepDuplicatingSchema

/-- Coefficient-based scalar barrier families. -/
inductive ScalarBarrierClass where
| additive
| affine
| restrictedQuadratic
| boundedCrossTermQuadratic
deriving DecidableEq, Repr

/-- Order flavors for the tracked-primary pair barriers. -/
inductive PrimaryPairBarrierClass where
| componentwise
| lex
deriving DecidableEq, Repr

/-- Standard coefficient-side pump witnesses visible in the formalized families. -/
inductive PumpFlag where
| succ
| wrap
deriving DecidableEq, Repr

/-- Normalized coefficient table for the richest scalar family formalized in the barrier
stack: affine `succ`/`wrap`, quadratic counter term, and one explicit step-counter cross term. -/
structure ScalarCoeffTable where
  c_base : Nat
  succ_bias : Nat
  succ_scale : Nat
  wrap_const : Nat
  wrap_left : Nat
  wrap_right : Nat
  recur_const : Nat
  recur_base : Nat
  recur_step : Nat
  recur_counter : Nat
  recur_quad : Nat
  recur_cross : Nat
deriving DecidableEq, Repr

/-- Primary-component coefficient table for the tracked pair barriers. The second component
is intentionally absent, because the current pair theorems only track the primary component. -/
structure PrimaryPairCoeffTable where
  order : PrimaryPairBarrierClass
  c_base1 : Nat
  succ_bias1 : Nat
  succ_scale1 : Nat
  wrap_const1 : Nat
  wrap_left1 : Nat
  wrap_right1 : Nat
  recur_const1 : Nat
  recur_base1 : Nat
  recur_step1 : Nat
  recur_counter1 : Nat
deriving DecidableEq, Repr

/-- Additive shape inside the normalized scalar table. -/
def ScalarCoeffTable.isAdditiveShape (C : ScalarCoeffTable) : Bool :=
  C.succ_scale = 1 &&
  C.wrap_left = 1 &&
  C.wrap_right = 1 &&
  C.recur_base = 1 &&
  C.recur_step = 1 &&
  C.recur_counter = 1 &&
  C.recur_quad = 0 &&
  C.recur_cross = 0

/-- Affine shape inside the normalized scalar table. -/
def ScalarCoeffTable.isAffineShape (C : ScalarCoeffTable) : Bool :=
  C.recur_quad = 0 && C.recur_cross = 0

/-- Restricted-quadratic shape: one pure counter-square term, but no cross term. -/
def ScalarCoeffTable.isRestrictedQuadraticShape (C : ScalarCoeffTable) : Bool :=
  C.recur_cross = 0

/-- Positive wrapper sensitivity required by the scalar barrier theorems. -/
def ScalarCoeffTable.hasPositiveWrapSensitivity (C : ScalarCoeffTable) : Bool :=
  1 ≤ C.wrap_left && 1 ≤ C.wrap_right

/-- Successor-pump side condition visible directly from the coefficients. -/
def ScalarCoeffTable.hasSuccPump (C : ScalarCoeffTable) : Bool :=
  1 ≤ C.succ_bias && 1 ≤ C.succ_scale

/-- Wrap/base pump side condition visible directly from the coefficients. -/
def ScalarCoeffTable.hasWrapPump (C : ScalarCoeffTable) : Bool :=
  1 ≤ C.wrap_const + C.wrap_right * C.c_base

/-- Bounded-regime side condition for the cross-term quadratic barrier, evaluated directly
on the normalized coefficient table. -/
def ScalarCoeffTable.crossTermBoundedAtBase (C : ScalarCoeffTable) : Bool :=
  let succBase := C.succ_bias + C.succ_scale * C.c_base
  C.recur_step + C.recur_cross * succBase + 1 ≤
    C.wrap_left + C.wrap_right * (C.recur_step + C.recur_cross * C.c_base)

/-- All structural scalar classes inhabited by the coefficient table, ordered from smaller
to larger. -/
def ScalarCoeffTable.structuralClasses (C : ScalarCoeffTable) : List ScalarBarrierClass :=
  let acc := []
  let acc := if C.isAdditiveShape then ScalarBarrierClass.additive :: acc else acc
  let acc := if C.isAffineShape then ScalarBarrierClass.affine :: acc else acc
  let acc := if C.isRestrictedQuadraticShape then ScalarBarrierClass.restrictedQuadratic :: acc else acc
  let acc := ScalarBarrierClass.boundedCrossTermQuadratic :: acc
  acc.reverse

/-- Standard pump flags visible directly from a scalar coefficient table. -/
def ScalarCoeffTable.pumpFlags (C : ScalarCoeffTable) : List PumpFlag :=
  let acc := []
  let acc := if C.hasSuccPump then PumpFlag.succ :: acc else acc
  let acc := if C.hasWrapPump then PumpFlag.wrap :: acc else acc
  acc.reverse

/-- The tracked-primary pair class is determined by the chosen order flavor. -/
def PrimaryPairCoeffTable.barrierClass (C : PrimaryPairCoeffTable) : PrimaryPairBarrierClass :=
  C.order

/-- Standard primary-component pump flags visible directly from the tracked pair table. -/
def PrimaryPairCoeffTable.pumpFlags (C : PrimaryPairCoeffTable) : List PumpFlag :=
  let acc := []
  let acc := if (1 ≤ C.succ_bias1 && 1 ≤ C.succ_scale1) then PumpFlag.succ :: acc else acc
  let acc := if (1 ≤ C.wrap_const1 + C.wrap_right1 * C.c_base1) then PumpFlag.wrap :: acc else acc
  acc.reverse

/-- Convert an additive measure to the normalized scalar coefficient table. -/
def AdditiveMeasure.toScalarCoeffTable {S : StepDuplicatingSchema}
    (M : AdditiveMeasure S) : ScalarCoeffTable where
  c_base := M.w_base
  succ_bias := M.w_succ
  succ_scale := 1
  wrap_const := M.w_wrap
  wrap_left := 1
  wrap_right := 1
  recur_const := M.w_recur
  recur_base := 1
  recur_step := 1
  recur_counter := 1
  recur_quad := 0
  recur_cross := 0

/-- Convert an affine measure to the normalized scalar coefficient table. -/
def AffineMeasure.toScalarCoeffTable {S : StepDuplicatingSchema}
    (M : AffineMeasure S) : ScalarCoeffTable where
  c_base := M.c_base
  succ_bias := M.succ_bias
  succ_scale := M.succ_scale
  wrap_const := M.wrap_const
  wrap_left := M.wrap_left
  wrap_right := M.wrap_right
  recur_const := M.recur_const
  recur_base := M.recur_base
  recur_step := M.recur_step
  recur_counter := M.recur_counter
  recur_quad := 0
  recur_cross := 0

/-- Convert a restricted-quadratic measure to the normalized scalar coefficient table. -/
def QuadraticCounterMeasure.toScalarCoeffTable {S : StepDuplicatingSchema}
    (M : QuadraticCounterMeasure S) : ScalarCoeffTable where
  c_base := M.c_base
  succ_bias := M.succ_bias
  succ_scale := M.succ_scale
  wrap_const := M.wrap_const
  wrap_left := M.wrap_left
  wrap_right := M.wrap_right
  recur_const := M.recur_const
  recur_base := M.recur_base
  recur_step := M.recur_step
  recur_counter := M.recur_counter
  recur_quad := M.recur_quad
  recur_cross := 0

/-- Convert a bounded cross-term quadratic measure to the normalized scalar coefficient table. -/
def CrossTermQuadraticMeasure.toScalarCoeffTable {S : StepDuplicatingSchema}
    (M : CrossTermQuadraticMeasure S) : ScalarCoeffTable where
  c_base := M.c_base
  succ_bias := M.succ_bias
  succ_scale := M.succ_scale
  wrap_const := M.wrap_const
  wrap_left := M.wrap_left
  wrap_right := M.wrap_right
  recur_const := M.recur_const
  recur_base := M.recur_base
  recur_step := M.recur_step
  recur_counter := M.recur_counter
  recur_quad := M.recur_quad
  recur_cross := M.recur_cross

/-- Convert the tracked-primary componentwise pair barrier data to a coefficient table. -/
def MatrixMeasure2.toPrimaryPairCoeffTableComponentwise {S : StepDuplicatingSchema}
    (M : MatrixMeasure2 S) : PrimaryPairCoeffTable where
  order := .componentwise
  c_base1 := M.c_base1
  succ_bias1 := M.succ_bias1
  succ_scale1 := M.succ_scale1
  wrap_const1 := M.wrap_const1
  wrap_left1 := M.wrap_left1
  wrap_right1 := M.wrap_right1
  recur_const1 := M.recur_const1
  recur_base1 := M.recur_base1
  recur_step1 := M.recur_step1
  recur_counter1 := M.recur_counter1

/-- Convert the tracked-primary lexicographic pair barrier data to a coefficient table. -/
def MatrixMeasure2.toPrimaryPairCoeffTableLex {S : StepDuplicatingSchema}
    (M : MatrixMeasure2 S) : PrimaryPairCoeffTable where
  order := .lex
  c_base1 := M.c_base1
  succ_bias1 := M.succ_bias1
  succ_scale1 := M.succ_scale1
  wrap_const1 := M.wrap_const1
  wrap_left1 := M.wrap_left1
  wrap_right1 := M.wrap_right1
  recur_const1 := M.recur_const1
  recur_base1 := M.recur_base1
  recur_step1 := M.recur_step1
  recur_counter1 := M.recur_counter1

/-- Soundness: additive measures classify as additive, affine, restricted quadratic,
and bounded cross-term tables. -/
theorem additive_table_classes {S : StepDuplicatingSchema} (M : AdditiveMeasure S) :
    M.toScalarCoeffTable.structuralClasses =
      [ ScalarBarrierClass.additive
      , ScalarBarrierClass.affine
      , ScalarBarrierClass.restrictedQuadratic
      , ScalarBarrierClass.boundedCrossTermQuadratic ] := by
  simp [AdditiveMeasure.toScalarCoeffTable, ScalarCoeffTable.structuralClasses,
    ScalarCoeffTable.isAdditiveShape, ScalarCoeffTable.isAffineShape,
    ScalarCoeffTable.isRestrictedQuadraticShape]

/-- Soundness: affine measures classify at least as affine, restricted quadratic, and bounded
cross-term tables. -/
theorem affine_table_classes {S : StepDuplicatingSchema} (M : AffineMeasure S) :
    M.toScalarCoeffTable.structuralClasses =
      (if M.succ_scale = 1 && M.wrap_left = 1 && M.wrap_right = 1 &&
            M.recur_base = 1 && M.recur_step = 1 && M.recur_counter = 1
        then [ ScalarBarrierClass.additive
             , ScalarBarrierClass.affine
             , ScalarBarrierClass.restrictedQuadratic
             , ScalarBarrierClass.boundedCrossTermQuadratic ]
        else [ ScalarBarrierClass.affine
             , ScalarBarrierClass.restrictedQuadratic
             , ScalarBarrierClass.boundedCrossTermQuadratic ]) := by
  by_cases hAdd :
      M.succ_scale = 1 && M.wrap_left = 1 && M.wrap_right = 1 &&
        M.recur_base = 1 && M.recur_step = 1 && M.recur_counter = 1
  · simp [AffineMeasure.toScalarCoeffTable, ScalarCoeffTable.structuralClasses,
      ScalarCoeffTable.isAdditiveShape, ScalarCoeffTable.isAffineShape,
      ScalarCoeffTable.isRestrictedQuadraticShape, hAdd]
  · simp [AffineMeasure.toScalarCoeffTable, ScalarCoeffTable.structuralClasses,
      ScalarCoeffTable.isAdditiveShape, ScalarCoeffTable.isAffineShape,
      ScalarCoeffTable.isRestrictedQuadraticShape, hAdd]

/-- Soundness: restricted quadratic measures classify at least as restricted quadratic and
bounded cross-term tables. -/
theorem quadratic_table_classes {S : StepDuplicatingSchema} (M : QuadraticCounterMeasure S) :
    M.toScalarCoeffTable.structuralClasses =
      (if M.recur_quad = 0 then
        if M.succ_scale = 1 && M.wrap_left = 1 && M.wrap_right = 1 &&
              M.recur_base = 1 && M.recur_step = 1 && M.recur_counter = 1 then
          [ ScalarBarrierClass.additive
          , ScalarBarrierClass.affine
          , ScalarBarrierClass.restrictedQuadratic
          , ScalarBarrierClass.boundedCrossTermQuadratic ]
        else
          [ ScalarBarrierClass.affine
          , ScalarBarrierClass.restrictedQuadratic
          , ScalarBarrierClass.boundedCrossTermQuadratic ]
      else
        [ ScalarBarrierClass.restrictedQuadratic
        , ScalarBarrierClass.boundedCrossTermQuadratic ]) := by
  by_cases hq : M.recur_quad = 0
  · by_cases hAdd :
        M.succ_scale = 1 && M.wrap_left = 1 && M.wrap_right = 1 &&
          M.recur_base = 1 && M.recur_step = 1 && M.recur_counter = 1
    · simp [QuadraticCounterMeasure.toScalarCoeffTable, ScalarCoeffTable.structuralClasses,
        ScalarCoeffTable.isAdditiveShape, ScalarCoeffTable.isAffineShape,
        ScalarCoeffTable.isRestrictedQuadraticShape, hq, hAdd]
    · simp [QuadraticCounterMeasure.toScalarCoeffTable, ScalarCoeffTable.structuralClasses,
        ScalarCoeffTable.isAdditiveShape, ScalarCoeffTable.isAffineShape,
        ScalarCoeffTable.isRestrictedQuadraticShape, hq, hAdd]
  · simp [QuadraticCounterMeasure.toScalarCoeffTable, ScalarCoeffTable.structuralClasses,
      ScalarCoeffTable.isAdditiveShape, ScalarCoeffTable.isAffineShape,
      ScalarCoeffTable.isRestrictedQuadraticShape, hq]

/-- Soundness: bounded cross-term quadratic measures always classify at least in the largest
coefficient-based scalar family. -/
theorem cross_table_has_top_class {S : StepDuplicatingSchema} (M : CrossTermQuadraticMeasure S) :
    ScalarBarrierClass.boundedCrossTermQuadratic ∈ M.toScalarCoeffTable.structuralClasses := by
  simp [CrossTermQuadraticMeasure.toScalarCoeffTable, ScalarCoeffTable.structuralClasses]

/-- Soundness: tracked-primary pair tables recover their declared order flavor. -/
theorem matrix2_componentwise_table_class {S : StepDuplicatingSchema} (M : MatrixMeasure2 S) :
    M.toPrimaryPairCoeffTableComponentwise.barrierClass = .componentwise := rfl

/-- Soundness: tracked-primary pair lex tables recover their declared order flavor. -/
theorem matrix2_lex_table_class {S : StepDuplicatingSchema} (M : MatrixMeasure2 S) :
    M.toPrimaryPairCoeffTableLex.barrierClass = .lex := rfl

end StepDuplicatingSchema
end StepDuplicating
