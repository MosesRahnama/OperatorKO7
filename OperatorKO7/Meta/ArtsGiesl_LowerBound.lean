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

end OperatorKO7.ArtsGieslLowerBound
