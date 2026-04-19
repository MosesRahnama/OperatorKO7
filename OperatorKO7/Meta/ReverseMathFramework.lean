import OperatorKO7.Meta.ReverseMathSupport

/-!
# Reverse-Mathematical Calibration Framework

Shared abstraction layer for the broader reverse-mathematical expansion
program in Paper 2.

This file does **not** prove a new calibration theorem by itself. Instead it
provides the reusable objects needed to express:

- theory profiles;
- principle profiles;
- implication / conservativity / equivalence relations between theory profiles;
- upper-bound / lower-bound / calibration records with explicit evidence
  status;
- concrete framework-level instances for SCT and the Arts--Giesl license.

The key design constraint is honesty: the framework must distinguish
theorem-level results from profile-level support and from conjectural
candidate calibrations.
-/

namespace OperatorKO7.ReverseMathFramework

open Ordinal
open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.ReverseMathSupport

/-- Evidence status attached to a calibration claim. -/
inductive EvidenceStatus
  | theoremLevel
  | profileLevel
  | conjectural
  deriving DecidableEq, Repr

/-- Coarse second-order theory profile used by the reverse-mathematical layer.

`ordinalCeiling?` is optional because not every paper-facing theory datum in
this repository is currently tied to an exact ordinal assignment.
-/
structure SecondOrderTheoryProfile where
  label : String
  theory : FormalTheory
  ordinalCeiling? : Option Ordinal := none
  complexityFloor? : Option FormulaClass := none

/-- Abstract proof-principle profile. This stays intentionally lightweight:
it records only the paper-facing identity, family, and complexity tags that
are already part of the mechanized register.
-/
structure PrincipleProfile where
  label : String
  family? : Option AscentFamily := none
  complexity? : Option FormulaClass := none

/-- A coarse implication witness between theory profiles: the source theory is
no stronger than the target theory on the existing formal-theory register.
-/
structure TheoryImplication (src dst : SecondOrderTheoryProfile) where
  carries : src.theory ≤ dst.theory

/-- A coarse conservativity witness between theory profiles. At the current
artifact level this means:

- the source theory embeds into the target theory on the paper's register; and
- no new ordinal ceiling is claimed beyond the one already attached to the
  source profile.
-/
structure TheoryConservativity (src dst : SecondOrderTheoryProfile) where
  extensionLe : src.theory ≤ dst.theory
  preservesOrdinalCeiling :
    match src.ordinalCeiling?, dst.ordinalCeiling? with
    | some α, some β => α = β
    | _, _ => True

/-- Bidirectional coarse equivalence between theory profiles. -/
structure TheoryEquivalence (left right : SecondOrderTheoryProfile) where
  forward : TheoryImplication left right
  backward : TheoryImplication right left

/-- A reverse-mathematical upper bound for a principle profile. The evidence
status makes explicit whether the bound is theorem-level, profile-level, or
still conjectural.
-/
structure ReverseMathUpperBound (P : PrincipleProfile) where
  theoryProfile : SecondOrderTheoryProfile
  evidenceStatus : EvidenceStatus
  justificationTag : String

/-- Lower-bound companion to `ReverseMathUpperBound`. -/
structure ReverseMathLowerBound (P : PrincipleProfile) where
  theoryProfile : SecondOrderTheoryProfile
  evidenceStatus : EvidenceStatus
  justificationTag : String

/-- General calibration package. This is the reusable object the roadmap was
calling for: it allows exact, profile-level, and conjectural calibrations to
be represented without pretending they are all theorem-level closures.
-/
structure ReverseMathCalibration (P : PrincipleProfile) where
  targetProfile : SecondOrderTheoryProfile
  upperBound : ReverseMathUpperBound P
  lowerBound? : Option (ReverseMathLowerBound P) := none
  targetLeUpper : targetProfile.theory ≤ upperBound.theoryProfile.theory
  lowerLeTarget :
    match lowerBound? with
    | none => True
    | some lb => lb.theoryProfile.theory ≤ targetProfile.theory
  status : CalibrationStatus

/-- Witness-bearing exact-calibration transport between proof principles.

This is intentionally stronger than a shared-target or status-only note: it
packages

- a source exact calibration,
- an explicit witness-preserving constant-overhead transport, and
- theorem-level destination upper/lower packages whose theory profiles match
  the source target exactly.

Within the coarse reverse-mathematical framework used by this repository, such
an object is enough to transfer exact calibration from the source principle to
the destination principle without appealing to external prose. -/
structure ExactCalibrationTransfer
    (src dst : PrincipleProfile) where
  sourceCalibration : ReverseMathCalibration src
  sourceExact : sourceCalibration.status = CalibrationStatus.exact
  witnessTransport : ConstantOverheadTransformation
  dstUpper : ReverseMathUpperBound dst
  dstLower : ReverseMathLowerBound dst
  upperMatchesSourceTarget : dstUpper.theoryProfile = sourceCalibration.targetProfile
  lowerMatchesSourceTarget : dstLower.theoryProfile = sourceCalibration.targetProfile
  upperTheoremLevel : dstUpper.evidenceStatus = EvidenceStatus.theoremLevel
  lowerTheoremLevel : dstLower.evidenceStatus = EvidenceStatus.theoremLevel

namespace SecondOrderTheoryProfile

@[simp] theorem theoryImplication_refl (A : SecondOrderTheoryProfile) :
    TheoryImplication A A := ⟨Nat.le_refl _⟩

@[simp] theorem theoryEquivalence_refl (A : SecondOrderTheoryProfile) :
    TheoryEquivalence A A := ⟨theoryImplication_refl A, theoryImplication_refl A⟩

end SecondOrderTheoryProfile

namespace ReverseMathCalibration

/-- Every calibration package already contains an upper bound by construction. -/
theorem has_upperBound {P : PrincipleProfile} (C : ReverseMathCalibration P) :
    C.targetProfile.theory ≤ C.upperBound.theoryProfile.theory :=
  C.targetLeUpper

end ReverseMathCalibration

namespace ExactCalibrationTransfer

/-- Assemble an exact destination calibration from a witness-bearing exact
transport object. -/
noncomputable def transferredCalibration
    {src dst : PrincipleProfile}
    (T : ExactCalibrationTransfer src dst) :
    ReverseMathCalibration dst where
  targetProfile := T.sourceCalibration.targetProfile
  upperBound := T.dstUpper
  lowerBound? := some T.dstLower
  targetLeUpper := by
    rw [T.upperMatchesSourceTarget]
    cases T.sourceCalibration.targetProfile.theory <;> decide
  lowerLeTarget := by
    change T.dstLower.theoryProfile.theory ≤ T.sourceCalibration.targetProfile.theory
    rw [T.lowerMatchesSourceTarget]
    cases T.sourceCalibration.targetProfile.theory <;> decide
  status := CalibrationStatus.exact

@[simp] theorem transferredCalibration_status
    {src dst : PrincipleProfile}
    (T : ExactCalibrationTransfer src dst) :
    T.transferredCalibration.status = CalibrationStatus.exact := rfl

@[simp] theorem transferredCalibration_targetProfile
    {src dst : PrincipleProfile}
    (T : ExactCalibrationTransfer src dst) :
    T.transferredCalibration.targetProfile = T.sourceCalibration.targetProfile := rfl

@[simp] theorem transferredCalibration_upperBound
    {src dst : PrincipleProfile}
    (T : ExactCalibrationTransfer src dst) :
    T.transferredCalibration.upperBound = T.dstUpper := rfl

@[simp] theorem transferredCalibration_lowerBound
    {src dst : PrincipleProfile}
    (T : ExactCalibrationTransfer src dst) :
    T.transferredCalibration.lowerBound? = some T.dstLower := rfl

theorem transferredCalibration_supported
    {src dst : PrincipleProfile}
    (T : ExactCalibrationTransfer src dst) :
    T.transferredCalibration.status = CalibrationStatus.exact
      ∧ T.transferredCalibration.upperBound.evidenceStatus = EvidenceStatus.theoremLevel
      ∧ (match T.transferredCalibration.lowerBound? with
          | some lb => lb.evidenceStatus = EvidenceStatus.theoremLevel
          | none => False) := by
  constructor
  · rfl
  constructor
  · simpa using T.upperTheoremLevel
  · simpa using T.lowerTheoremLevel

end ExactCalibrationTransfer

/-! ## Concrete framework-level profiles already supported by the artifact -/

/-- Base theory profile for `PRA`. -/
def praTheoryProfile : SecondOrderTheoryProfile where
  label := "PRA"
  theory := FormalTheory.PRA

/-- Base theory profile for `IΣ₁`. -/
def iSigma1TheoryProfile : SecondOrderTheoryProfile where
  label := "IΣ₁"
  theory := FormalTheory.ISigma1
  complexityFloor? := some FormulaClass.pi02

/-- Base theory profile for `RCA₀`. -/
def rca0TheoryProfile : SecondOrderTheoryProfile where
  label := "RCA₀"
  theory := FormalTheory.RCA0

/-- Base theory profile for `RCA₀ + WO(ω^3)`. -/
noncomputable def rca0WoOmega3TheoryProfile : SecondOrderTheoryProfile where
  label := "RCA₀ + WO(ω^3)"
  theory := FormalTheory.RCA0_WO_omega3
  ordinalCeiling? := some omegaPowThree

/-- Base theory profile for the current `ε₀` benchmark. -/
noncomputable def woEpsilon0TheoryProfile : SecondOrderTheoryProfile where
  label := "WO(ε₀)"
  theory := FormalTheory.WO_epsilon0
  ordinalCeiling? := some ε₀

/-- Principle profile for the Arts--Giesl soundness license. -/
def artsGieslPrincipleProfile : PrincipleProfile where
  label := "Arts--Giesl soundness"
  family? := some artsGieslLicenseProfile.family
  complexity? := some artsGieslLicenseProfile.complexity

/-- Principle profile for SCT as the adjacent exact calibration point used in
the paper. The family and formula-class tags are intentionally left absent
because they are not currently proved in this repository.
-/
def sctPrincipleProfile : PrincipleProfile where
  label := "Size-change termination"

/-- Theorem-level exact upper bound for SCT. -/
noncomputable def sctExactUpperBound : ReverseMathUpperBound sctPrincipleProfile where
  theoryProfile := rca0WoOmega3TheoryProfile
  evidenceStatus := EvidenceStatus.theoremLevel
  justificationTag := "sctReverseMathProfile"

/-- Theorem-level exact lower bound for SCT. -/
noncomputable def sctExactLowerBound : ReverseMathLowerBound sctPrincipleProfile where
  theoryProfile := rca0WoOmega3TheoryProfile
  evidenceStatus := EvidenceStatus.theoremLevel
  justificationTag := "sctReverseMathProfile"

/-- Exact SCT calibration package. -/
noncomputable def sctExactCalibration : ReverseMathCalibration sctPrincipleProfile where
  targetProfile := rca0WoOmega3TheoryProfile
  upperBound := sctExactUpperBound
  lowerBound? := some sctExactLowerBound
  targetLeUpper := by
    show FormalTheory.RCA0_WO_omega3 ≤ FormalTheory.RCA0_WO_omega3
    decide
  lowerLeTarget := by
    show FormalTheory.RCA0_WO_omega3 ≤ FormalTheory.RCA0_WO_omega3
    decide
  status := CalibrationStatus.exact

/-- Candidate upper bound package for the Arts--Giesl target. This is
intentionally marked conjectural: the framework distinguishes the current
support profile from a proved semantic upper-bound theorem.
-/
noncomputable def artsGieslCandidateUpperBound :
    ReverseMathUpperBound artsGieslPrincipleProfile where
  theoryProfile := woEpsilon0TheoryProfile
  evidenceStatus := EvidenceStatus.conjectural
  justificationTag := "artsGieslReverseMathCalibration.upperBenchmark"

/-- Candidate lower bound package for the Arts--Giesl target. This matches the
paper's current target object rather than a proved theorem.
-/
noncomputable def artsGieslCandidateLowerBound :
    ReverseMathLowerBound artsGieslPrincipleProfile where
  theoryProfile := rca0WoOmega3TheoryProfile
  evidenceStatus := EvidenceStatus.conjectural
  justificationTag := "artsGieslReverseMathCalibration.target"

/-- Conjectural Arts--Giesl calibration package in framework form. -/
noncomputable def artsGieslConjecturalCalibration :
    ReverseMathCalibration artsGieslPrincipleProfile where
  targetProfile := rca0WoOmega3TheoryProfile
  upperBound := artsGieslCandidateUpperBound
  lowerBound? := some artsGieslCandidateLowerBound
  targetLeUpper := by
    show FormalTheory.RCA0_WO_omega3 ≤ FormalTheory.WO_epsilon0
    decide
  lowerLeTarget := by
    show FormalTheory.RCA0_WO_omega3 ≤ FormalTheory.RCA0_WO_omega3
    decide
  status := CalibrationStatus.conjectural

/-- The framework-level SCT calibration is exact. -/
@[simp] theorem sctExactCalibration_status :
    sctExactCalibration.status = CalibrationStatus.exact := rfl

/-- The framework-level AG calibration remains conjectural. -/
@[simp] theorem artsGieslConjecturalCalibration_status :
    artsGieslConjecturalCalibration.status = CalibrationStatus.conjectural := rfl

/-- The AG target theory matches the SCT exact target at the current framework
level. -/
theorem artsGiesl_and_sct_share_framework_target_theory :
    artsGieslConjecturalCalibration.targetProfile.theory =
      sctExactCalibration.targetProfile.theory := by
  simp [artsGieslConjecturalCalibration, sctExactCalibration,
    rca0WoOmega3TheoryProfile]

/-- The AG and SCT framework profiles share the same explicit ordinal target. -/
theorem artsGiesl_and_sct_share_framework_target_ordinal :
    artsGieslConjecturalCalibration.targetProfile.ordinalCeiling? =
      sctExactCalibration.targetProfile.ordinalCeiling? := by
  rfl

/-- The theorem-level SCT exact calibration sits below the current `ε₀`
benchmark profile on the coarse theory register. -/
noncomputable def sctIntoEpsilon0Implication :
    TheoryImplication rca0WoOmega3TheoryProfile woEpsilon0TheoryProfile where
  carries := by decide

/-- The conjectural Arts--Giesl target sits below its current benchmark on the
coarse theory register. -/
theorem artsGiesl_framework_target_below_benchmark :
    artsGieslConjecturalCalibration.targetProfile.theory ≤
      artsGieslConjecturalCalibration.upperBound.theoryProfile.theory := by
  show FormalTheory.RCA0_WO_omega3 ≤ FormalTheory.WO_epsilon0
  decide

end OperatorKO7.ReverseMathFramework
