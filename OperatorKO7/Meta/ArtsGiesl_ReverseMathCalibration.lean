import OperatorKO7.Meta.ArtsGiesl_LowerBound

/-!
# Arts--Giesl Reverse-Mathematical Calibration

Current best calibration package for the Arts--Giesl soundness license.

This module is deliberately honest:
- the upper bound is theorem-level;
- the lower bound is theorem-level but coarse;
- the target itself remains conjectural.
-/

namespace OperatorKO7.ArtsGieslReverseMathCalibration

open Ordinal
open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.ReverseMathSupport
open OperatorKO7.ReverseMathFramework
open OperatorKO7.ArtsGieslUpperBound
open OperatorKO7.ArtsGieslLowerBound

/-- Best current calibration object for the Arts--Giesl soundness license.
The exact target remains conjectural, but it is now bracketed by theorem-level
upper- and lower-bound packages inside one public object. -/
noncomputable def artsGieslCurrentCalibration : ReverseMathCalibration artsGieslPrincipleProfile where
  targetProfile := rca0WoOmega3TheoryProfile
  upperBound := artsGieslTheoremUpperBound
  lowerBound? := some artsGieslTheoremLowerBound
  targetLeUpper := artsGiesl_targetTheory_le_theoremUpperBound
  lowerLeTarget := artsGieslTheoremLowerBound_le_target
  status := CalibrationStatus.conjectural

@[simp] theorem artsGieslCurrentCalibration_status :
    artsGieslCurrentCalibration.status = CalibrationStatus.conjectural := rfl

@[simp] theorem artsGieslCurrentCalibration_target_theory :
    artsGieslCurrentCalibration.targetProfile.theory = FormalTheory.RCA0_WO_omega3 := rfl

@[simp] theorem artsGieslCurrentCalibration_target_ordinal :
    artsGieslCurrentCalibration.targetProfile.ordinalCeiling? = some omegaPowThree := rfl

/-- The current calibration object carries a theorem-level upper bound. -/
theorem artsGieslCurrentCalibration_has_theoremUpperBound :
    artsGieslCurrentCalibration.upperBound.evidenceStatus = EvidenceStatus.theoremLevel :=
  artsGieslTheoremUpperBound_status

/-- The current calibration object also carries a theorem-level lower bound,
though only in the current coarse `RCA₀` + `Π⁰₂` sense. -/
theorem artsGieslCurrentCalibration_has_theoremLowerBound :
    match artsGieslCurrentCalibration.lowerBound? with
    | some lb => lb.evidenceStatus = EvidenceStatus.theoremLevel
    | none => False := by
  simp [artsGieslCurrentCalibration, artsGieslTheoremLowerBound_status]

/-- The target remains below the theorem-level `ε₀` benchmark tracked by the
artifact. -/
theorem artsGieslCurrentCalibration_below_safe_measure :
    artsGieslCurrentCalibration.targetProfile.ordinalCeiling? = some omegaPowThree
      ∧ omegaPowThree < ko7SafeMeasureUpperBound.upper := by
  constructor
  · rfl
  · simpa [ko7SafeMeasureUpperBound] using omegaPowThree_lt_epsilon0

/-- The current calibration agrees with the existing SCT target on both theory
and ordinal, while keeping its own conjectural status. -/
theorem artsGieslCurrentCalibration_matches_sct_reference :
    artsGieslCurrentCalibration.targetProfile.theory = sctExactCalibration.targetProfile.theory
      ∧ artsGieslCurrentCalibration.targetProfile.ordinalCeiling? =
          sctExactCalibration.targetProfile.ordinalCeiling?
      ∧ artsGieslCurrentCalibration.status = CalibrationStatus.conjectural := by
  constructor
  · rfl
  constructor
  · rfl
  · rfl

/-- Summary theorem for the current AG calibration layer. -/
theorem artsGieslCurrentCalibration_supported :
    artsGieslCurrentCalibration.status = CalibrationStatus.conjectural
      ∧ artsGieslCurrentCalibration.targetProfile.theory = FormalTheory.RCA0_WO_omega3
      ∧ artsGieslCurrentCalibration.upperBound.evidenceStatus = EvidenceStatus.theoremLevel
      ∧ (match artsGieslCurrentCalibration.lowerBound? with
          | some lb => lb.evidenceStatus = EvidenceStatus.theoremLevel
          | none => False) := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · exact artsGieslTheoremUpperBound_status
  · simp [artsGieslCurrentCalibration, artsGieslTheoremLowerBound_status]

end OperatorKO7.ArtsGieslReverseMathCalibration
