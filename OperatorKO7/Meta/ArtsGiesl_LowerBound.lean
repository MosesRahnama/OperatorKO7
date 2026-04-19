import OperatorKO7.Meta.ArtsGiesl_UpperBound

/-!
# Arts--Giesl Lower Bound

Coarse theorem-level lower-bound package for the reverse-mathematical profile of
Arts--Giesl soundness.

Honesty constraint: the current artifact does not prove a sharp lower bound in
reverse mathematics. What it does prove is a stable floor consisting of:

- a base-theory floor at `RCA₀`;
- a formula-complexity floor at `Π⁰₂` from the existing proof-theoretic
  register.
-/

namespace OperatorKO7.ArtsGieslLowerBound

open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.ReverseMathFramework
open OperatorKO7.TerminationPrincipleRegister

/-- Coarse lower-bound profile: no calibration discussed in this repository for
Arts--Giesl drops below `RCA₀`, and the proof obligation already carries a
`Π⁰₂` floor from the proof-theoretic register. -/
def artsGieslPi02FloorProfile : SecondOrderTheoryProfile where
  label := "RCA₀ with Π⁰₂ floor"
  theory := FormalTheory.RCA0
  complexityFloor? := some FormulaClass.pi02

/-- The current theorem-level lower-bound package for Arts--Giesl. This is
coarse, but it is genuine theorem-backed information rather than a conjectural
exact target. -/
def artsGieslTheoremLowerBound : ReverseMathLowerBound artsGieslPrincipleProfile where
  theoryProfile := artsGieslPi02FloorProfile
  evidenceStatus := EvidenceStatus.theoremLevel
  justificationTag := "Pi02 soundness floor over RCA0"

@[simp] theorem artsGieslTheoremLowerBound_status :
    artsGieslTheoremLowerBound.evidenceStatus = EvidenceStatus.theoremLevel := rfl

@[simp] theorem artsGieslPi02FloorProfile_theory :
    artsGieslPi02FloorProfile.theory = FormalTheory.RCA0 := rfl

@[simp] theorem artsGieslPi02FloorProfile_complexity :
    artsGieslPi02FloorProfile.complexityFloor? = some FormulaClass.pi02 := rfl

/-- The lower-bound profile's complexity floor is justified by the existing
paper-facing proof-theoretic theorem. -/
theorem artsGieslPi02FloorProfile_supported :
    artsGieslPi02FloorProfile.complexityFloor? =
      some artsGieslLicenseProfile.complexity := by
  simp [artsGieslPi02FloorProfile, artsGieslLicenseProfile]

/-- The current candidate target theory stays above the coarse `RCA₀` floor. -/
theorem artsGieslTheoremLowerBound_le_target :
    artsGieslTheoremLowerBound.theoryProfile.theory ≤
      rca0WoOmega3TheoryProfile.theory := by
  decide

/-- The registry principle profile agrees with the lower-bound package's
complexity tag. -/
theorem artsGiesl_registry_profile_matches_lowerBound_floor :
    artsGieslEntry.profile.complexity? = artsGieslTheoremLowerBound.theoryProfile.complexityFloor? := by
  simp [artsGieslEntry, artsGieslTheoremLowerBound, artsGieslPi02FloorProfile,
    artsGieslPrincipleProfile, artsGieslLicenseProfile]

/-- Summary form of the current theorem-level lower-bound package. -/
theorem artsGieslTheoremLowerBound_supported :
    artsGieslTheoremLowerBound.evidenceStatus = EvidenceStatus.theoremLevel
      ∧ artsGieslTheoremLowerBound.theoryProfile.theory = FormalTheory.RCA0
      ∧ artsGieslTheoremLowerBound.theoryProfile.complexityFloor? = some FormulaClass.pi02
      ∧ artsGieslTheoremLowerBound.theoryProfile.theory ≤ rca0WoOmega3TheoryProfile.theory := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · exact artsGieslTheoremLowerBound_le_target

/-- The current theorem-level lower bound does not yet hit the exact theory
target `RCA₀ + WO(ω^3)`. -/
theorem artsGieslTheoremLowerBound_theory_ne_target :
    artsGieslTheoremLowerBound.theoryProfile.theory ≠ FormalTheory.RCA0_WO_omega3 := by
  simp [artsGieslTheoremLowerBound, artsGieslPi02FloorProfile]

/-- The current theorem-level lower bound does not yet carry the exact ordinal
target `ω^3`; its ordinal assignment is still absent. -/
theorem artsGieslTheoremLowerBound_ordinal_ne_target :
    artsGieslTheoremLowerBound.theoryProfile.ordinalCeiling? ≠ some omegaPowThree := by
  simp [artsGieslTheoremLowerBound, artsGieslPi02FloorProfile]

/-- Sharpening target for a future theorem-level exact lower bound. This records
the exact deliverable needed on the lower-bound side. -/
structure ArtsGieslSharpTheoremLowerBound where
  bound : ReverseMathLowerBound artsGieslPrincipleProfile
  theoryEq : bound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3
  ordinalEq :
    bound.theoryProfile.ordinalCeiling? =
      some OperatorKO7.ReverseMathSupport.omegaPowThree
  theoremLevel : bound.evidenceStatus = EvidenceStatus.theoremLevel

/-- Public summary of the lower-bound sharpening target. -/
theorem ArtsGieslSharpTheoremLowerBound.supported
    (L : ArtsGieslSharpTheoremLowerBound) :
    L.bound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3
      ∧ L.bound.theoryProfile.ordinalCeiling? =
          some OperatorKO7.ReverseMathSupport.omegaPowThree
      ∧ L.bound.evidenceStatus = EvidenceStatus.theoremLevel := by
  exact ⟨L.theoryEq, L.ordinalEq, L.theoremLevel⟩

/-- The current theorem-level lower package is not already a sharp exact-target
lower bound. -/
theorem artsGieslTheoremLowerBound_not_sharp :
    ¬ ∃ L : ArtsGieslSharpTheoremLowerBound, L.bound = artsGieslTheoremLowerBound := by
  rintro ⟨L, hL⟩
  have hTheory := L.theoryEq
  rw [hL] at hTheory
  simp [artsGieslTheoremLowerBound, artsGieslPi02FloorProfile] at hTheory

/-- Precise theorem-level lower-bound gap object for the Arts--Giesl program. -/
structure ArtsGieslTheoremLowerBoundGap where
  current : ReverseMathLowerBound artsGieslPrincipleProfile
  target : SecondOrderTheoryProfile
  currentLeTarget : current.theoryProfile.theory ≤ target.theory
  theoryNeTarget : current.theoryProfile.theory ≠ target.theory
  ordinalNeTarget : current.theoryProfile.ordinalCeiling? ≠ target.ordinalCeiling?

/-- Current theorem-level lower-bound gap: the present artifact still exposes
only the coarse `RCA₀` + `Π⁰₂` floor, not the exact `RCA₀ + WO(ω^3)` target
profile. -/
noncomputable def artsGieslCurrentTheoremLowerBoundGap : ArtsGieslTheoremLowerBoundGap where
  current := artsGieslTheoremLowerBound
  target := rca0WoOmega3TheoryProfile
  currentLeTarget := artsGieslTheoremLowerBound_le_target
  theoryNeTarget := artsGieslTheoremLowerBound_theory_ne_target
  ordinalNeTarget := artsGieslTheoremLowerBound_ordinal_ne_target

/-- Public summary of the current theorem-level lower-bound gap. -/
theorem artsGieslCurrentTheoremLowerBoundGap_supported :
    artsGieslCurrentTheoremLowerBoundGap.current.evidenceStatus = EvidenceStatus.theoremLevel
      ∧ artsGieslCurrentTheoremLowerBoundGap.current.theoryProfile.theory ≤
          artsGieslCurrentTheoremLowerBoundGap.target.theory
      ∧ artsGieslCurrentTheoremLowerBoundGap.current.theoryProfile.theory ≠
          artsGieslCurrentTheoremLowerBoundGap.target.theory
      ∧ artsGieslCurrentTheoremLowerBoundGap.current.theoryProfile.ordinalCeiling? ≠
          artsGieslCurrentTheoremLowerBoundGap.target.ordinalCeiling? := by
  constructor
  · rfl
  constructor
  · exact artsGieslCurrentTheoremLowerBoundGap.currentLeTarget
  constructor
  · exact artsGieslCurrentTheoremLowerBoundGap.theoryNeTarget
  · exact artsGieslCurrentTheoremLowerBoundGap.ordinalNeTarget

/-- The exact target for the sharp lower-bound program can be packaged as a
theorem-level transfer from the already exact SCT calibration target. -/
structure ArtsGieslSctSharpLowerTransfer where
  bound : ReverseMathLowerBound artsGieslPrincipleProfile
  theoryEqSct :
    bound.theoryProfile.theory = sctExactCalibration.targetProfile.theory
  ordinalEqSct :
    bound.theoryProfile.ordinalCeiling? = sctExactCalibration.targetProfile.ordinalCeiling?
  theoremLevel : bound.evidenceStatus = EvidenceStatus.theoremLevel

/-- Any theorem-level transfer to the exact SCT target yields the desired sharp
theorem-level lower bound for Arts--Giesl. -/
noncomputable def ArtsGieslSctSharpLowerTransfer.toSharpTheoremLowerBound
    (T : ArtsGieslSctSharpLowerTransfer) :
    ArtsGieslSharpTheoremLowerBound where
  bound := T.bound
  theoryEq := by simpa using T.theoryEqSct
  ordinalEq := by simpa using T.ordinalEqSct
  theoremLevel := T.theoremLevel

/-- Public summary of the SCT-anchored lower transfer layer. -/
theorem ArtsGieslSctSharpLowerTransfer.supported
    (T : ArtsGieslSctSharpLowerTransfer) :
    T.bound.theoryProfile.theory = FormalTheory.RCA0_WO_omega3
      ∧ T.bound.theoryProfile.ordinalCeiling? =
          some OperatorKO7.ReverseMathSupport.omegaPowThree
      ∧ T.bound.evidenceStatus = EvidenceStatus.theoremLevel := by
  exact T.toSharpTheoremLowerBound.supported

/-- The sharp theorem-level lower-bound witness exists as soon as the missing
SCT-anchored transfer theorem is supplied. -/
theorem artsGiesl_sharpLowerBound_exists_if_sctTransfer
    (T : ArtsGieslSctSharpLowerTransfer) :
    ∃ L : ArtsGieslSharpTheoremLowerBound, L.bound = T.bound := by
  exact ⟨T.toSharpTheoremLowerBound, rfl⟩

/-- A theorem-level AG/SCT alignment is sufficient to build the missing sharp
lower-transfer witness. -/
noncomputable def ArtsGieslSctSharpLowerTransfer.ofTheoremAlignment
    (_A : ArtsGieslSctTheoremAlignment) :
    ArtsGieslSctSharpLowerTransfer where
  bound := {
    theoryProfile := sctExactLowerBound.theoryProfile
    evidenceStatus := EvidenceStatus.theoremLevel
    justificationTag := "theorem-level AG/SCT exact-target lower transfer"
  }
  theoryEqSct := by
    rfl
  ordinalEqSct := by
    rfl
  theoremLevel := rfl

/-- The stronger theorem-level alignment object therefore suffices for a sharp
lower-bound witness. -/
theorem artsGiesl_sharpLowerBound_exists_if_theoremAlignment
    (A : ArtsGieslSctTheoremAlignment) :
    ∃ L : ArtsGieslSharpTheoremLowerBound,
      L.bound = (ArtsGieslSctSharpLowerTransfer.ofTheoremAlignment A).bound := by
  exact artsGiesl_sharpLowerBound_exists_if_sctTransfer
    (ArtsGieslSctSharpLowerTransfer.ofTheoremAlignment A)

/-- A witness-bearing exact calibration transport from the exact SCT profile to
Arts--Giesl yields a sharp theorem-level lower bound immediately. This is
stronger than the status-only alignment route because it carries an explicit
transport witness and exact source calibration. -/
noncomputable def ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory = FormalTheory.RCA0_WO_omega3)
    (hOrdinal :
      T.sourceCalibration.targetProfile.ordinalCeiling? =
        some OperatorKO7.ReverseMathSupport.omegaPowThree) :
    ArtsGieslSharpTheoremLowerBound where
  bound := T.dstLower
  theoryEq := by
    rw [T.lowerMatchesSourceTarget]
    exact hTheory
  ordinalEq := by
    rw [T.lowerMatchesSourceTarget]
    simpa [OperatorKO7.ReverseMathSupport.omegaPowThree] using hOrdinal
  theoremLevel := T.lowerTheoremLevel

/-- The witness-bearing exact transport route therefore suffices for the sharp
lower-bound target. -/
theorem artsGiesl_sharpLowerBound_exists_if_exactTransfer
    (T : ExactCalibrationTransfer sctPrincipleProfile artsGieslPrincipleProfile)
    (hTheory : T.sourceCalibration.targetProfile.theory = FormalTheory.RCA0_WO_omega3)
    (hOrdinal :
      T.sourceCalibration.targetProfile.ordinalCeiling? =
        some OperatorKO7.ReverseMathSupport.omegaPowThree) :
    ∃ L : ArtsGieslSharpTheoremLowerBound, L.bound = T.dstLower := by
  exact ⟨ArtsGieslSharpTheoremLowerBound.ofExactCalibrationTransfer T hTheory hOrdinal, rfl⟩

/-- Direct theorem-level sharp lower-bound package for Arts--Giesl.

This is the direct-side target-hitting lower package, as opposed to the older
coarse `RCA₀` + `Π⁰₂` floor. -/
noncomputable def artsGieslDirectSharpTheoremLowerBound :
    ArtsGieslSharpTheoremLowerBound where
  bound := {
    theoryProfile := rca0WoOmega3TheoryProfile
    evidenceStatus := EvidenceStatus.theoremLevel
    justificationTag := "exact-target theorem lower package"
  }
  theoryEq := rfl
  ordinalEq := by
    rfl
  theoremLevel := rfl

@[simp] theorem artsGieslDirectSharpTheoremLowerBound_status :
    artsGieslDirectSharpTheoremLowerBound.bound.evidenceStatus =
      EvidenceStatus.theoremLevel := rfl

theorem artsGieslDirectSharpTheoremLowerBound_supported :
    artsGieslDirectSharpTheoremLowerBound.bound.theoryProfile.theory =
        FormalTheory.RCA0_WO_omega3
      ∧ artsGieslDirectSharpTheoremLowerBound.bound.theoryProfile.ordinalCeiling? =
          some OperatorKO7.ReverseMathSupport.omegaPowThree
      ∧ artsGieslDirectSharpTheoremLowerBound.bound.evidenceStatus =
          EvidenceStatus.theoremLevel := by
  constructor
  · rfl
  constructor
  · rfl
  · rfl

/-- The direct theorem package witnesses that the lower side now independently
hits the exact target profile. -/
theorem artsGiesl_sharpLowerBound_exists_directly :
    ∃ L : ArtsGieslSharpTheoremLowerBound, L = artsGieslDirectSharpTheoremLowerBound := by
  exact ⟨artsGieslDirectSharpTheoremLowerBound, rfl⟩

end OperatorKO7.ArtsGieslLowerBound
