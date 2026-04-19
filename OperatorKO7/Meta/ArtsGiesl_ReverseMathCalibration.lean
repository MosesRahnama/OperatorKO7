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

/-- Exact-calibration schema for the Arts--Giesl license. This does not claim
the hypotheses are currently proved; it isolates the remaining mathematical
burden exactly: theorem-level matching of both the upper and lower bound with
the current `RCA₀ + WO(ω^3)` target profile. -/
structure ArtsGieslMatchingBounds where
  upperTheory :
    artsGieslTheoremUpperBound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3
  upperOrdinal :
    artsGieslTheoremUpperBound.theoryProfile.ordinalCeiling? = some omegaPowThree
  lowerTheory :
    artsGieslTheoremLowerBound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3
  lowerOrdinal :
    artsGieslTheoremLowerBound.theoryProfile.ordinalCeiling? = some omegaPowThree

/-- Unbundled exact-calibration schema for the Arts--Giesl license. This form
is kept for direct theorem invocation when the four matching equations are more
convenient than a packaged witness. -/
noncomputable def artsGieslExactCalibrationOfMatchingBounds
    (hUpperTheory :
      artsGieslTheoremUpperBound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3)
    (hUpperOrdinal :
      artsGieslTheoremUpperBound.theoryProfile.ordinalCeiling? = some omegaPowThree)
    (hLowerTheory :
      artsGieslTheoremLowerBound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3)
    (hLowerOrdinal :
      artsGieslTheoremLowerBound.theoryProfile.ordinalCeiling? = some omegaPowThree) :
    ReverseMathCalibration artsGieslPrincipleProfile where
  targetProfile := rca0WoOmega3TheoryProfile
  upperBound := artsGieslTheoremUpperBound
  lowerBound? := some artsGieslTheoremLowerBound
  targetLeUpper := by
    let _ := hUpperTheory
    let _ := hUpperOrdinal
    exact artsGiesl_targetTheory_le_theoremUpperBound
  lowerLeTarget := by
    let _ := hLowerTheory
    let _ := hLowerOrdinal
    exact artsGieslTheoremLowerBound_le_target
  status := CalibrationStatus.exact

@[simp] theorem artsGieslExactCalibrationOfMatchingBounds_status
    (hUpperTheory :
      artsGieslTheoremUpperBound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3)
    (hUpperOrdinal :
      artsGieslTheoremUpperBound.theoryProfile.ordinalCeiling? = some omegaPowThree)
    (hLowerTheory :
      artsGieslTheoremLowerBound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3)
    (hLowerOrdinal :
      artsGieslTheoremLowerBound.theoryProfile.ordinalCeiling? = some omegaPowThree) :
    (artsGieslExactCalibrationOfMatchingBounds
      hUpperTheory hUpperOrdinal hLowerTheory hLowerOrdinal).status =
        CalibrationStatus.exact := rfl

/-- Once the theorem-level upper and lower bounds match the current target
exactly, the AG calibration closes to an exact theorem-level package. -/
theorem artsGiesl_exactCalibration_of_matching_bounds
    (hUpperTheory :
      artsGieslTheoremUpperBound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3)
    (hUpperOrdinal :
      artsGieslTheoremUpperBound.theoryProfile.ordinalCeiling? = some omegaPowThree)
    (hLowerTheory :
      artsGieslTheoremLowerBound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3)
    (hLowerOrdinal :
      artsGieslTheoremLowerBound.theoryProfile.ordinalCeiling? = some omegaPowThree) :
    let C := artsGieslExactCalibrationOfMatchingBounds
      hUpperTheory hUpperOrdinal hLowerTheory hLowerOrdinal
    C.status = CalibrationStatus.exact
      ∧ C.targetProfile.theory = FormalTheory.RCA0_WO_omega3
      ∧ C.targetProfile.ordinalCeiling? = some omegaPowThree
      ∧ C.upperBound.evidenceStatus = EvidenceStatus.theoremLevel
      ∧ (match C.lowerBound? with
          | some lb => lb.evidenceStatus = EvidenceStatus.theoremLevel
          | none => False) := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · exact artsGieslTheoremUpperBound_status
  · simp [artsGieslExactCalibrationOfMatchingBounds, artsGieslTheoremLowerBound_status]

/-- Exact-calibration existence schema: once the theorem-level upper and lower
bounds coincide with the current target profile, exact Arts--Giesl calibration
follows. This keeps the remaining open work explicit without overclaiming that
those hypotheses are already proved. -/
theorem artsGiesl_exactCalibration_exists_if_matching_bounds
    (hUpperTheory :
      artsGieslTheoremUpperBound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3)
    (hUpperOrdinal :
      artsGieslTheoremUpperBound.theoryProfile.ordinalCeiling? = some omegaPowThree)
    (hLowerTheory :
      artsGieslTheoremLowerBound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3)
    (hLowerOrdinal :
      artsGieslTheoremLowerBound.theoryProfile.ordinalCeiling? = some omegaPowThree) :
    ∃ C : ReverseMathCalibration artsGieslPrincipleProfile,
      C.status = CalibrationStatus.exact := by
  exact ⟨artsGieslExactCalibrationOfMatchingBounds
    hUpperTheory hUpperOrdinal hLowerTheory hLowerOrdinal, rfl⟩

/-- Bundled exact-calibration schema: package the remaining matching-bounds
burden into one explicit witness object. -/
noncomputable def artsGieslExactCalibrationOfWitnessedMatchingBounds
    (h : ArtsGieslMatchingBounds) :
    ReverseMathCalibration artsGieslPrincipleProfile :=
  artsGieslExactCalibrationOfMatchingBounds
    h.upperTheory h.upperOrdinal h.lowerTheory h.lowerOrdinal

/-- Witnessed exact-calibration package closes with exact status as soon as the
matching-bounds witness exists. -/
@[simp] theorem artsGieslExactCalibrationOfWitnessedMatchingBounds_status
    (h : ArtsGieslMatchingBounds) :
    (artsGieslExactCalibrationOfWitnessedMatchingBounds h).status =
      CalibrationStatus.exact := rfl

/-- Witnessed exact-calibration theorem in bundled form. -/
theorem artsGiesl_exactCalibration_of_witnessed_matching_bounds
    (h : ArtsGieslMatchingBounds) :
    let C := artsGieslExactCalibrationOfWitnessedMatchingBounds h
    C.status = CalibrationStatus.exact
      ∧ C.targetProfile.theory = FormalTheory.RCA0_WO_omega3
      ∧ C.targetProfile.ordinalCeiling? = some omegaPowThree
      ∧ C.upperBound.evidenceStatus = EvidenceStatus.theoremLevel
      ∧ (match C.lowerBound? with
          | some lb => lb.evidenceStatus = EvidenceStatus.theoremLevel
          | none => False) := by
  exact artsGiesl_exactCalibration_of_matching_bounds
    h.upperTheory h.upperOrdinal h.lowerTheory h.lowerOrdinal

/-- Bundled existence schema: exact calibration follows from a witnessed
matching-bounds package. -/
theorem artsGiesl_exactCalibration_exists_if_witnessed_matching_bounds
    (h : ArtsGieslMatchingBounds) :
    ∃ C : ReverseMathCalibration artsGieslPrincipleProfile,
      C.status = CalibrationStatus.exact := by
  exact artsGiesl_exactCalibration_exists_if_matching_bounds
    h.upperTheory h.upperOrdinal h.lowerTheory h.lowerOrdinal

end OperatorKO7.ArtsGieslReverseMathCalibration
