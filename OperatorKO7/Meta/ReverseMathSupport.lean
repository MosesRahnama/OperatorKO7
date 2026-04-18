import OperatorKO7.Meta.ProofTheoreticRegister
import OperatorKO7.Meta.DM_OrderType
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Exponential

/-!
# Reverse-Mathematical Support Library

This module lifts the paper-facing reverse-mathematical bookkeeping into a
reusable support layer.

It provides:

- theory calibration windows;
- ordinal calibration windows;
- shared exact/conjectural calibration profiles for SCT and Arts--Giesl;
- compatibility theorems connecting the AG target to the existing `ε₀`
  ordinal surface already mechanized for KO7;
- a constant-overhead transformation model capturing the recursor-side
  Arts--Giesl license overhead.

The goal is not to prove the reverse-mathematical conjecture itself. The goal
is to give it enough internal structure that it can be compared, transported,
and strengthened without remaining an isolated named constant.
-/

namespace OperatorKO7.ReverseMathSupport

open Ordinal
open OperatorKO7.ProofTheoreticRegister

/-- Calibration status for a proof-theoretic profile. -/
inductive CalibrationStatus
  | exact
  | conjectural
  | boundedUpper
  deriving DecidableEq, Repr

/-- Theory-level calibration window. -/
structure TheoryCalibrationWindow where
  lowerTheory : FormalTheory
  targetTheory : FormalTheory
  upperTheory : FormalTheory
  lowerLeTarget : lowerTheory ≤ targetTheory
  targetLeUpper : targetTheory ≤ upperTheory
  status : CalibrationStatus

/-- Ordinal-level calibration window. -/
structure OrdinalCalibrationWindow where
  lowerOrdinal : Ordinal
  targetOrdinal : Ordinal
  upperOrdinal : Ordinal
  lowerLtTarget : lowerOrdinal < targetOrdinal
  targetLtUpper : targetOrdinal < upperOrdinal
  status : CalibrationStatus

/-- Combined reverse-mathematical profile for a soundness license. -/
structure ReverseMathProfile where
  license : OperatorKO7.ConfessionMethodFamily.SoundnessLicense
  theoryWindow : TheoryCalibrationWindow
  ordinalWindow : OrdinalCalibrationWindow

/-- The paper's `ω^3` target as an explicit ordinal constant. -/
noncomputable def omegaPowThree : Ordinal := (ω : Ordinal) ^ (3 : Ordinal)

/-- The existing DM-side `ω^ω` benchmark as an explicit ordinal constant. -/
noncomputable def omegaPowOmega : Ordinal := (ω : Ordinal) ^ (ω : Ordinal)

@[simp] theorem omegaPowThree_def :
    omegaPowThree = (ω : Ordinal) ^ (3 : Ordinal) := rfl

@[simp] theorem omegaPowOmega_def :
    omegaPowOmega = (ω : Ordinal) ^ (ω : Ordinal) := rfl

/-- The `ω^3` target is strictly below the already mechanized `ω^ω` barrier. -/
theorem omegaPowThree_lt_omegaPowOmega :
    omegaPowThree < omegaPowOmega := by
  dsimp [omegaPowThree, omegaPowOmega]
  exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2
    (by simpa using (Ordinal.nat_lt_omega0 3))

/-- Therefore `ω^3` is also strictly below `ε₀`. -/
theorem omegaPowThree_lt_epsilon0 :
    omegaPowThree < ε₀ := by
  exact lt_trans omegaPowThree_lt_omegaPowOmega OperatorKO7.MetaDM.opow_omega_lt_epsilon0

/-- Reference theory window for the exact SCT calibration at `RCA₀ + WO(ω^3)`. -/
def sctTheoryWindow : TheoryCalibrationWindow where
  lowerTheory := FormalTheory.RCA0
  targetTheory := FormalTheory.RCA0_WO_omega3
  upperTheory := FormalTheory.WO_epsilon0
  lowerLeTarget := by decide
  targetLeUpper := by decide
  status := CalibrationStatus.exact

/-- Reference ordinal window for the exact SCT calibration at `ω^3`. -/
noncomputable def sctOrdinalWindow : OrdinalCalibrationWindow where
  lowerOrdinal := 0
  targetOrdinal := omegaPowThree
  upperOrdinal := ε₀
  lowerLtTarget := by
    dsimp [omegaPowThree]
    exact Ordinal.opow_pos (3 : Ordinal) Ordinal.omega0_pos
  targetLtUpper := omegaPowThree_lt_epsilon0
  status := CalibrationStatus.exact

/-- Exact SCT reverse-mathematical calibration profile used as the adjacent
reference point for the AG conjecture. -/
noncomputable def sctReverseMathProfile : ReverseMathProfile where
  license := OperatorKO7.ConfessionMethodFamily.SoundnessLicense.leeJonesBenAmram2001
  theoryWindow := sctTheoryWindow
  ordinalWindow := sctOrdinalWindow

/-- Theory window induced by the AG conjectural target already recorded in the
paper-facing proof-theoretic register. -/
def artsGieslTheoryWindow : TheoryCalibrationWindow where
  lowerTheory := FormalTheory.RCA0
  targetTheory := artsGieslReverseMathCalibration.target
  upperTheory := artsGieslReverseMathCalibration.upperBenchmark
  lowerLeTarget := by decide
  targetLeUpper := by decide
  status := CalibrationStatus.conjectural

/-- Ordinal window matching the AG conjectural `ω^3` target. -/
noncomputable def artsGieslOrdinalWindow : OrdinalCalibrationWindow where
  lowerOrdinal := 0
  targetOrdinal := omegaPowThree
  upperOrdinal := ε₀
  lowerLtTarget := by
    dsimp [omegaPowThree]
    exact Ordinal.opow_pos (3 : Ordinal) Ordinal.omega0_pos
  targetLtUpper := omegaPowThree_lt_epsilon0
  status := CalibrationStatus.conjectural

/-- Strengthened reverse-mathematical profile for the Arts--Giesl license. -/
noncomputable def artsGieslReverseMathProfile : ReverseMathProfile where
  license := OperatorKO7.ConfessionMethodFamily.SoundnessLicense.artsGiesl2000
  theoryWindow := artsGieslTheoryWindow
  ordinalWindow := artsGieslOrdinalWindow

@[simp] theorem artsGieslTheoryWindow_target :
    artsGieslTheoryWindow.targetTheory = FormalTheory.RCA0_WO_omega3 := by
  simp [artsGieslTheoryWindow, arts_giesl_reverse_math_target]

@[simp] theorem artsGieslTheoryWindow_upper :
    artsGieslTheoryWindow.upperTheory = FormalTheory.WO_epsilon0 := rfl

@[simp] theorem artsGieslTheoryWindow_status :
    artsGieslTheoryWindow.status = CalibrationStatus.conjectural := rfl

@[simp] theorem artsGieslOrdinalWindow_status :
    artsGieslOrdinalWindow.status = CalibrationStatus.conjectural := rfl

@[simp] theorem sctTheoryWindow_status :
    sctTheoryWindow.status = CalibrationStatus.exact := rfl

@[simp] theorem sctOrdinalWindow_status :
    sctOrdinalWindow.status = CalibrationStatus.exact := rfl

/-- The AG theory target agrees with the SCT reference target. -/
theorem artsGiesl_and_sct_share_theory_target :
    artsGieslReverseMathProfile.theoryWindow.targetTheory =
      sctReverseMathProfile.theoryWindow.targetTheory := by
  simp [artsGieslReverseMathProfile, sctReverseMathProfile,
    artsGieslTheoryWindow, sctTheoryWindow]

/-- The AG ordinal target agrees with the SCT reference target. -/
theorem artsGiesl_and_sct_share_ordinal_target :
    artsGieslReverseMathProfile.ordinalWindow.targetOrdinal =
      sctReverseMathProfile.ordinalWindow.targetOrdinal := by
  rfl

/-- The AG conjectural target sits strictly below the paper's `ε₀` benchmark. -/
theorem artsGiesl_target_strictly_below_epsilon0 :
    artsGieslReverseMathProfile.ordinalWindow.targetOrdinal < ε₀ := by
  simpa [artsGieslReverseMathProfile, artsGieslOrdinalWindow] using omegaPowThree_lt_epsilon0

/-- The SCT reference target also sits strictly below the `ε₀` benchmark. -/
theorem sct_target_strictly_below_epsilon0 :
    sctReverseMathProfile.ordinalWindow.targetOrdinal < ε₀ := by
  simpa [sctReverseMathProfile, sctOrdinalWindow] using omegaPowThree_lt_epsilon0

/-- Artifact-side ordinal upper-bound package. -/
structure ArtifactOrdinalUpperBound where
  carrier : Type
  rank : carrier → Ordinal
  upper : Ordinal
  bounded : ∀ x, rank x < upper

/-- The existing KO7 `μ₃ᶜ` / DM order-type stack already supplies an `ε₀`
upper bound. This packages that fact for reuse in reverse-mathematical
comparisons. -/
noncomputable def ko7SafeMeasureUpperBound : ArtifactOrdinalUpperBound where
  carrier := OperatorKO7.Trace
  rank := fun t => OperatorKO7.MetaDM.lex3cToOrd (OperatorKO7.MetaCM.mu3c t)
  upper := ε₀
  bounded := OperatorKO7.MetaDM.safeMeasure_below_epsilon0

/-- The AG conjectural ordinal target sits below the currently mechanized KO7
artifact benchmark. -/
theorem artsGiesl_target_below_ko7_safe_measure_upper :
    artsGieslReverseMathProfile.ordinalWindow.targetOrdinal < ko7SafeMeasureUpperBound.upper := by
  simpa [ko7SafeMeasureUpperBound] using artsGiesl_target_strictly_below_epsilon0

/-- The SCT reference target also sits below the same benchmark. -/
theorem sct_target_below_ko7_safe_measure_upper :
    sctReverseMathProfile.ordinalWindow.targetOrdinal < ko7SafeMeasureUpperBound.upper := by
  simpa [ko7SafeMeasureUpperBound] using sct_target_strictly_below_epsilon0

/-- Constant-overhead transformation model. This is the right abstraction for
proof-method transformations that preserve the underlying witness language up to
uniform finite assembly cost. -/
structure ConstantOverheadTransformation where
  overhead : Nat
  transformedCost : Nat → Nat
  exactShape : ∀ n, transformedCost n = n + overhead

/-- Constant-overhead transformations preserve affine linear growth in the
strongest exact form available in this repository. -/
theorem ConstantOverheadTransformation.preserves_affine_linear_shape
    (T : ConstantOverheadTransformation) (n : Nat) :
    T.transformedCost n = n + T.overhead :=
  T.exactShape n

/-- The recursor-side Arts--Giesl license application is a constant-overhead
transformation of the residual proof work. -/
def agRecursorTransformation : ConstantOverheadTransformation where
  overhead := agLicenseOverhead
  transformedCost := fun n =>
    OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.residualProofWork n
      + agLicenseOverhead
  exactShape := ag_proof_length_on_step_duplicating_recursor

@[simp] theorem agRecursorTransformation_overhead :
    agRecursorTransformation.overhead = agLicenseOverhead := rfl

/-- The recursor-side AG transformation preserves linear certificate growth up
to the exact constant assembly overhead. -/
theorem agRecursorTransformation_preserves_linear_growth (n : Nat) :
    agRecursorTransformation.transformedCost n = n + agRecursorTransformation.overhead := by
  simp [agRecursorTransformation,
    ConstantOverheadTransformation.preserves_affine_linear_shape]

/-- The AG reverse-mathematical support layer is no longer just a conjectural
constant: it now shares both target theory and target ordinal with the SCT
reference window, and it sits below the existing `ε₀` artifact benchmark. -/
theorem artsGiesl_profile_supported_by_sct_and_epsilon0 :
    artsGieslReverseMathProfile.theoryWindow.targetTheory =
        sctReverseMathProfile.theoryWindow.targetTheory
      ∧ artsGieslReverseMathProfile.ordinalWindow.targetOrdinal =
          sctReverseMathProfile.ordinalWindow.targetOrdinal
      ∧ artsGieslReverseMathProfile.ordinalWindow.targetOrdinal <
          ko7SafeMeasureUpperBound.upper := by
  constructor
  · simp [artsGieslReverseMathProfile, sctReverseMathProfile,
      artsGieslTheoryWindow, sctTheoryWindow, arts_giesl_reverse_math_target]
  constructor
  · rfl
  · simpa [ko7SafeMeasureUpperBound, artsGieslReverseMathProfile,
      artsGieslOrdinalWindow] using omegaPowThree_lt_epsilon0

/-- Universe-stable public summary theorem for the AG reverse-mathematical
support layer. -/
theorem artsGiesl_supported_summary :
    artsGieslReverseMathProfile.theoryWindow.targetTheory = FormalTheory.RCA0_WO_omega3
      ∧ artsGieslReverseMathProfile.ordinalWindow.targetOrdinal = omegaPowThree
      ∧ artsGieslReverseMathProfile.ordinalWindow.targetOrdinal < ε₀ := by
  constructor
  · simp [artsGieslReverseMathProfile, artsGieslTheoryWindow,
      arts_giesl_reverse_math_target]
  constructor
  · rfl
  · simpa [artsGieslReverseMathProfile, artsGieslOrdinalWindow] using
      omegaPowThree_lt_epsilon0

end OperatorKO7.ReverseMathSupport
