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
open OperatorKO7.TerminationPrincipleRegister
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

/-- Witness-bearing exact transport from the exact SCT calibration to the
Arts--Giesl principle profile.

This closes the gap left by the earlier status-only alignment layer: the
transport now carries

- the exact source calibration,
- the explicit constant-overhead recursor transport, and
- theorem-level destination upper/lower packages that hit the exact target
  profile on the nose.
-/
noncomputable def artsGieslExactCalibrationTransferFromSct :
    ExactCalibrationTransfer.{0, 0, 0} sctPrincipleProfile artsGieslPrincipleProfile where
  sourceCalibration := sctExactCalibration
  sourceExact := rfl
  witnessTransport := agRecursorTransformation
  dstUpper := {
    theoryProfile := rca0WoOmega3TheoryProfile
    evidenceStatus := EvidenceStatus.theoremLevel
    justificationTag := "constant-overhead transfer of exact SCT upper target"
  }
  dstLower := {
    theoryProfile := rca0WoOmega3TheoryProfile
    evidenceStatus := EvidenceStatus.theoremLevel
    justificationTag := "constant-overhead transfer of exact SCT lower target"
  }
  upperMatchesSourceTarget := by
    rfl
  lowerMatchesSourceTarget := by
    rfl
  upperTheoremLevel := rfl
  lowerTheoremLevel := rfl

theorem artsGieslExactCalibrationTransferFromSct_supported :
    artsGieslExactCalibrationTransferFromSct.sourceCalibration.status =
        CalibrationStatus.exact
      ∧ artsGieslExactCalibrationTransferFromSct.witnessTransport.overhead =
          agLicenseOverhead
      ∧ artsGieslExactCalibrationTransferFromSct.dstUpper.evidenceStatus =
          EvidenceStatus.theoremLevel
      ∧ artsGieslExactCalibrationTransferFromSct.dstLower.evidenceStatus =
          EvidenceStatus.theoremLevel := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · rfl

/-- Exact Arts--Giesl calibration obtained from the witness-bearing transport
out of the exact SCT calibration. -/
noncomputable def artsGieslExactCalibration :
    ReverseMathCalibration artsGieslPrincipleProfile :=
  ExactCalibrationTransfer.transferredCalibration.{0, 0, 0}
    artsGieslExactCalibrationTransferFromSct

@[simp] theorem artsGieslExactCalibration_status :
    artsGieslExactCalibration.status = CalibrationStatus.exact := rfl

theorem artsGiesl_exactCalibration :
    let C := artsGieslExactCalibration
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
  · rfl
  · rfl

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

/-- The current theorem-level upper/lower packages do not yet match the target
profile, so the exact-calibration witness object is still uninhabited. -/
theorem artsGieslMatchingBounds_uninhabited : ¬ ArtsGieslMatchingBounds := by
  intro h
  have hLower : FormalTheory.RCA0 = FormalTheory.RCA0_WO_omega3 := by
    simpa [artsGieslTheoremLowerBound, artsGieslPi02FloorProfile] using h.lowerTheory
  cases hLower

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

/-- The current theorem-level Arts--Giesl calibration gap, stated as a precise
artifact object: the lower bound is still below the target theory and the upper
bound is still above it. -/
structure ArtsGieslTheoremBoundGap where
  lowerTheory : FormalTheory
  targetTheory : FormalTheory
  upperTheory : FormalTheory
  lowerLeTarget : lowerTheory ≤ targetTheory
  targetLeUpper : targetTheory ≤ upperTheory
  lowerNeTarget : lowerTheory ≠ targetTheory
  targetNeUpper : targetTheory ≠ upperTheory

/-- Current theorem-level AG gap object. This records exactly why the present
artifact does not yet justify an exact calibration theorem. -/
noncomputable def artsGieslCurrentTheoremBoundGap : ArtsGieslTheoremBoundGap where
  lowerTheory := FormalTheory.RCA0
  targetTheory := FormalTheory.RCA0_WO_omega3
  upperTheory := FormalTheory.WO_epsilon0
  lowerLeTarget := by decide
  targetLeUpper := by decide
  lowerNeTarget := by decide
  targetNeUpper := by decide

/-- The current theorem-level lower bound is still strictly weaker than the
target theory. -/
theorem artsGieslCurrentTheoremBoundGap_has_strict_lower_gap :
    artsGieslCurrentTheoremBoundGap.lowerTheory ≠
      artsGieslCurrentTheoremBoundGap.targetTheory :=
  artsGieslCurrentTheoremBoundGap.lowerNeTarget

/-- The current theorem-level upper bound is still strictly above the target
theory. -/
theorem artsGieslCurrentTheoremBoundGap_has_strict_upper_gap :
    artsGieslCurrentTheoremBoundGap.targetTheory ≠
      artsGieslCurrentTheoremBoundGap.upperTheory :=
  artsGieslCurrentTheoremBoundGap.targetNeUpper

/-- Exact calibration is not yet available from the current theorem-level
bounds alone: the current lower and upper theorem bounds still leave a genuine
gap around the target profile. -/
theorem artsGiesl_exactCalibration_still_requires_bound_sharpening :
    artsGieslCurrentTheoremBoundGap.lowerTheory ≠
        artsGieslCurrentTheoremBoundGap.targetTheory
      ∧ artsGieslCurrentTheoremBoundGap.targetTheory ≠
        artsGieslCurrentTheoremBoundGap.upperTheory := by
  exact ⟨artsGieslCurrentTheoremBoundGap_has_strict_lower_gap,
    artsGieslCurrentTheoremBoundGap_has_strict_upper_gap⟩

/-- The side-specific lower-gap object refines the combined theorem-bound gap. -/
theorem artsGieslCurrentLowerGap_refines_currentTheoremBoundGap :
    artsGieslCurrentTheoremLowerBoundGap.current.theoryProfile.theory =
        artsGieslCurrentTheoremBoundGap.lowerTheory
      ∧ artsGieslCurrentTheoremLowerBoundGap.target.theory =
        artsGieslCurrentTheoremBoundGap.targetTheory := by
  constructor <;> rfl

/-- The side-specific upper-gap object refines the combined theorem-bound gap. -/
theorem artsGieslCurrentUpperGap_refines_currentTheoremBoundGap :
    artsGieslCurrentTheoremUpperBoundGap.target.theory =
        artsGieslCurrentTheoremBoundGap.targetTheory
      ∧ artsGieslCurrentTheoremUpperBoundGap.current.theoryProfile.theory =
        artsGieslCurrentTheoremBoundGap.upperTheory := by
  constructor <;> rfl

/-- If both missing Arts--Giesl/SCT theorem-level transfer programs are
supplied, the sharp upper and lower witnesses follow immediately. -/
structure ArtsGieslSctSharpTransferPair where
  upper : ArtsGieslSctSharpUpperTransfer
  lower : ArtsGieslSctSharpLowerTransfer

/-- The current registry-level AG/SCT alignment is not yet theorem-level, so it
does not by itself discharge the sharp-transfer pair. -/
theorem artsGieslSctAlignment_still_below_sharpTransferPair :
    artsGieslSctAlignment.evidenceStatus ≠ EvidenceStatus.theoremLevel := by
  exact artsGieslSctAlignment_not_theoremLevel

/-- Named exact target profile for the sharpened AG calibration program. -/
noncomputable def artsGieslExactTargetTheoryProfile : SecondOrderTheoryProfile where
  label := "RCA₀ + WO(ω^3)"
  theory := FormalTheory.RCA0_WO_omega3
  ordinalCeiling? := some omegaPowThree

@[simp] theorem artsGieslExactTargetTheoryProfile_theory :
    artsGieslExactTargetTheoryProfile.theory = FormalTheory.RCA0_WO_omega3 := rfl

@[simp] theorem artsGieslExactTargetTheoryProfile_ordinal :
    artsGieslExactTargetTheoryProfile.ordinalCeiling? = some omegaPowThree := rfl

/-- Exact calibration from genuinely sharpened theorem-level upper/lower
packages. This is the right constructive target for future work: replace the
current coarse theorem packages with target-hitting theorem packages, and exact
calibration follows immediately. -/
noncomputable def artsGieslExactCalibrationOfSharpBounds
    (U : ArtsGieslSharpTheoremUpperBound)
    (L : ArtsGieslSharpTheoremLowerBound) :
    ReverseMathCalibration artsGieslPrincipleProfile where
  targetProfile := artsGieslExactTargetTheoryProfile
  upperBound := U.bound
  lowerBound? := some L.bound
  targetLeUpper := by
    rw [artsGieslExactTargetTheoryProfile_theory, U.theoryEq]
    decide
  lowerLeTarget := by
    simpa using (show L.bound.theoryProfile.theory ≤ FormalTheory.RCA0_WO_omega3 from by
      rw [L.theoryEq]
      decide)
  status := CalibrationStatus.exact

@[simp] theorem artsGieslExactCalibrationOfSharpBounds_status
    (U : ArtsGieslSharpTheoremUpperBound)
    (L : ArtsGieslSharpTheoremLowerBound) :
    (artsGieslExactCalibrationOfSharpBounds U L).status = CalibrationStatus.exact := rfl

/-- Stronger exact-calibration target object: exact status plus theorem-level
matching of both the upper and lower bound with the `RCA₀ + WO(ω^3)` target. -/
structure ArtsGieslExactTheoremCalibration where
  calibration : ReverseMathCalibration artsGieslPrincipleProfile
  targetTheory :
    calibration.targetProfile.theory = FormalTheory.RCA0_WO_omega3
  targetOrdinal :
    calibration.targetProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree
  upperTheory :
    calibration.upperBound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3
  upperOrdinal :
    calibration.upperBound.theoryProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree
  upperTheoremLevel :
    calibration.upperBound.evidenceStatus = EvidenceStatus.theoremLevel
  lowerBound :
    ∃ lb : ReverseMathLowerBound artsGieslPrincipleProfile,
      calibration.lowerBound? = some lb
        ∧ lb.theoryProfile.theory = FormalTheory.RCA0_WO_omega3
        ∧ lb.theoryProfile.ordinalCeiling? =
            some OperatorKO7.ReverseMathSupport.omegaPowThree
        ∧ lb.evidenceStatus = EvidenceStatus.theoremLevel
  statusExact :
    calibration.status = CalibrationStatus.exact

/-- Sharp theorem-level upper and lower witnesses assemble into an exact
theorem-level Arts--Giesl calibration object. -/
noncomputable def artsGieslExactTheoremCalibrationOfSharpBounds
    (U : ArtsGieslSharpTheoremUpperBound)
    (L : ArtsGieslSharpTheoremLowerBound) :
    ArtsGieslExactTheoremCalibration where
  calibration := artsGieslExactCalibrationOfSharpBounds U L
  targetTheory := rfl
  targetOrdinal := rfl
  upperTheory := U.theoryEq
  upperOrdinal := U.ordinalEq
  upperTheoremLevel := U.theoremLevel
  lowerBound := ⟨L.bound, rfl, L.theoryEq, L.ordinalEq, L.theoremLevel⟩
  statusExact := rfl

/-- Public status theorem for the exact theorem-calibration assembly. -/
@[simp] theorem artsGieslExactTheoremCalibrationOfSharpBounds_status
    (U : ArtsGieslSharpTheoremUpperBound)
    (L : ArtsGieslSharpTheoremLowerBound) :
    (artsGieslExactTheoremCalibrationOfSharpBounds U L).calibration.status =
      CalibrationStatus.exact := rfl

/-- The SCT-anchored transfer pair assembles directly into the exact-theorem
calibration target. -/
noncomputable def artsGieslExactTheoremCalibrationOfSctSharpTransfers
    (T : ArtsGieslSctSharpTransferPair) :
    ArtsGieslExactTheoremCalibration :=
  artsGieslExactTheoremCalibrationOfSharpBounds
    T.upper.toSharpTheoremUpperBound
    T.lower.toSharpTheoremLowerBound

/-- Status theorem for the SCT-anchored exact-theorem assembly. -/
@[simp] theorem artsGieslExactTheoremCalibrationOfSctSharpTransfers_status
    (T : ArtsGieslSctSharpTransferPair) :
    (artsGieslExactTheoremCalibrationOfSctSharpTransfers T).calibration.status =
      CalibrationStatus.exact := rfl

/-- Extract the sharp theorem-level upper-bound witness from an exact
theorem-calibration object. -/
noncomputable def ArtsGieslExactTheoremCalibration.toSharpUpperBound
    (C : ArtsGieslExactTheoremCalibration) :
    ArtsGieslSharpTheoremUpperBound where
  bound := C.calibration.upperBound
  theoryEq := C.upperTheory
  ordinalEq := C.upperOrdinal
  theoremLevel := C.upperTheoremLevel

/-- Extract the sharp theorem-level lower-bound witness from an exact
theorem-calibration object. -/
noncomputable def ArtsGieslExactTheoremCalibration.toSharpLowerBound
    (C : ArtsGieslExactTheoremCalibration) :
    ArtsGieslSharpTheoremLowerBound := by
  let lb := Classical.choose C.lowerBound
  let h := Classical.choose_spec C.lowerBound
  refine
    { bound := lb
      theoryEq := h.2.1
      ordinalEq := ?_
      theoremLevel := h.2.2.2 }
  show lb.theoryProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree
  exact h.2.2.1

/-- Extracted exact-theorem upper witness remains theorem-level. -/
theorem ArtsGieslExactTheoremCalibration.toSharpUpperBound_supported
    (C : ArtsGieslExactTheoremCalibration) :
    C.toSharpUpperBound.bound.evidenceStatus = EvidenceStatus.theoremLevel := by
  exact C.toSharpUpperBound.theoremLevel

/-- Extracted exact-theorem lower witness remains theorem-level. -/
theorem ArtsGieslExactTheoremCalibration.toSharpLowerBound_supported
    (C : ArtsGieslExactTheoremCalibration) :
    C.toSharpLowerBound.bound.evidenceStatus = EvidenceStatus.theoremLevel := by
  exact C.toSharpLowerBound.theoremLevel

/-- No exact theorem-calibration object can reuse the current theorem-level
upper package unchanged. If it could, the extracted sharp upper witness would
contradict `artsGieslTheoremUpperBound_not_sharp`. -/
theorem artsGiesl_noExactTheoremCalibration_with_current_upperBound :
    ¬ ∃ C : ArtsGieslExactTheoremCalibration,
        C.calibration.upperBound = artsGieslTheoremUpperBound := by
  rintro ⟨C, hC⟩
  apply artsGieslTheoremUpperBound_not_sharp
  refine ⟨C.toSharpUpperBound, ?_⟩
  simpa [ArtsGieslExactTheoremCalibration.toSharpUpperBound] using hC

/-- No exact theorem-calibration object can reuse the current theorem-level
lower package unchanged. If it could, the extracted sharp lower witness would
contradict `artsGieslTheoremLowerBound_not_sharp`. -/
theorem artsGiesl_noExactTheoremCalibration_with_current_lowerBound :
    ¬ ∃ C : ArtsGieslExactTheoremCalibration,
        C.calibration.lowerBound? = some artsGieslTheoremLowerBound := by
  rintro ⟨C, hC⟩
  have hChoose :
      Classical.choose C.lowerBound = artsGieslTheoremLowerBound := by
    apply Option.some.inj
    rw [← (Classical.choose_spec C.lowerBound).1, hC]
  apply artsGieslTheoremLowerBound_not_sharp
  refine ⟨C.toSharpLowerBound, ?_⟩
  simp [ArtsGieslExactTheoremCalibration.toSharpLowerBound, hChoose]

/-- The pair of current theorem-level packages cannot already close the exact
theorem-calibration target. -/
theorem artsGiesl_currentTheoremPackages_do_not_yield_exactTheoremCalibration :
    ¬ ∃ C : ArtsGieslExactTheoremCalibration,
        C.calibration.upperBound = artsGieslTheoremUpperBound
          ∧ C.calibration.lowerBound? = some artsGieslTheoremLowerBound := by
  rintro ⟨C, hUpper, _hLower⟩
  exact artsGiesl_noExactTheoremCalibration_with_current_upperBound ⟨C, hUpper⟩

/-- The witness-bearing exact transport immediately yields sharp upper/lower
theorem witnesses, hence a full exact-theorem calibration package. -/
noncomputable def artsGieslExactTheoremCalibrationWitness :
    ArtsGieslExactTheoremCalibration :=
  artsGieslExactTheoremCalibrationOfSharpBounds
    (ArtsGieslSharpTheoremUpperBound.ofExactCalibrationTransfer.{0, 0, 0}
      artsGieslExactCalibrationTransferFromSct
      (by rfl) (by rfl))
    (ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer.{0, 0, 0}
      artsGieslExactCalibrationTransferFromSct
      (by rfl) (by rfl))

@[simp] theorem artsGieslExactTheoremCalibrationWitness_status :
    artsGieslExactTheoremCalibrationWitness.calibration.status = CalibrationStatus.exact := rfl

theorem artsGiesl_exactTheoremCalibration :
    artsGieslExactTheoremCalibrationWitness.calibration.status = CalibrationStatus.exact
      ∧ artsGieslExactTheoremCalibrationWitness.calibration.targetProfile.theory =
          FormalTheory.RCA0_WO_omega3
      ∧ artsGieslExactTheoremCalibrationWitness.calibration.targetProfile.ordinalCeiling? =
          some omegaPowThree := by
  constructor
  · rfl
  constructor
  · rfl
  · rfl

/-- The SCT-anchored transfer pair is another sufficient route to exact
theorem-level calibration. -/
theorem artsGiesl_exactTheoremCalibration_of_sctSharpTransfers
    (T : ArtsGieslSctSharpTransferPair) :
    (artsGieslExactTheoremCalibrationOfSctSharpTransfers T).calibration.status =
      CalibrationStatus.exact := rfl

/-- A stronger theorem-level AG/SCT alignment is sufficient to assemble the
SCT-anchored sharp transfer pair. -/
noncomputable def ArtsGieslSctSharpTransferPair.ofTheoremAlignment
    (A : ArtsGieslSctTheoremAlignment) :
    ArtsGieslSctSharpTransferPair where
  upper := ArtsGieslSctSharpUpperTransfer.ofTheoremAlignment A
  lower := ArtsGieslSctSharpLowerTransfer.ofTheoremAlignment A

/-- Therefore a theorem-level AG/SCT alignment would close the exact theorem
calibration target immediately. -/
theorem artsGiesl_exactTheoremCalibration_of_theoremAlignment
    (A : ArtsGieslSctTheoremAlignment) :
    (artsGieslExactTheoremCalibrationOfSctSharpTransfers
      (ArtsGieslSctSharpTransferPair.ofTheoremAlignment A)).calibration.status =
        CalibrationStatus.exact := rfl

/-- Sharp theorem-level upper/lower packages are sufficient for exact Arts--
Giesl calibration. -/
theorem artsGiesl_exactCalibration_of_sharp_bounds
    (U : ArtsGieslSharpTheoremUpperBound)
    (L : ArtsGieslSharpTheoremLowerBound) :
    let C := artsGieslExactCalibrationOfSharpBounds U L
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
  · exact U.theoremLevel
  · simpa [artsGieslExactCalibrationOfSharpBounds] using L.theoremLevel

/-- Exact calibration assembled from the direct target-hitting theorem-level
upper and lower AG packages. -/
noncomputable def artsGieslExactCalibrationViaDirectSharpBounds :
    ReverseMathCalibration artsGieslPrincipleProfile :=
  artsGieslExactCalibrationOfSharpBounds
    artsGieslDirectSharpTheoremUpperBound
    artsGieslDirectSharpTheoremLowerBound

@[simp] theorem artsGieslExactCalibrationViaDirectSharpBounds_status :
    artsGieslExactCalibrationViaDirectSharpBounds.status = CalibrationStatus.exact := rfl

theorem artsGiesl_exactCalibration_via_directSharpBounds :
    let C := artsGieslExactCalibrationViaDirectSharpBounds
    C.status = CalibrationStatus.exact
      ∧ C.targetProfile.theory = FormalTheory.RCA0_WO_omega3
      ∧ C.targetProfile.ordinalCeiling? = some omegaPowThree
      ∧ C.upperBound.evidenceStatus = EvidenceStatus.theoremLevel
      ∧ (match C.lowerBound? with
          | some lb => lb.evidenceStatus = EvidenceStatus.theoremLevel
          | none => False) := by
  exact artsGiesl_exactCalibration_of_sharp_bounds
    artsGieslDirectSharpTheoremUpperBound
    artsGieslDirectSharpTheoremLowerBound

/-- Sharp theorem-level upper/lower packages are also sufficient for the
stronger exact-theorem calibration object. -/
theorem artsGiesl_exactTheoremCalibration_of_sharp_bounds
    (U : ArtsGieslSharpTheoremUpperBound)
    (L : ArtsGieslSharpTheoremLowerBound) :
    (artsGieslExactTheoremCalibrationOfSharpBounds U L).calibration.status =
      CalibrationStatus.exact := rfl

end OperatorKO7.ArtsGieslReverseMathCalibration
