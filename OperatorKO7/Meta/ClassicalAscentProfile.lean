import OperatorKO7.Meta.ReflectionSchema

/-!
# Classical Ascent Profile

Paper-facing comparison wrapper above `ReflectionSchema`.

This file packages the already mechanized DP-side profile as a classical-style
ascent profile and defines the exact compatibility condition any future
classical-side profile must satisfy before it can legitimately be compared to
that DP profile.
-/

namespace OperatorKO7.ClassicalAscentProfile

open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.ReflectionSchema

private theorem iff_of_true {P Q : Prop} (hP : P) (hQ : Q) : P ↔ Q := by
  constructor
  · intro _
    exact hQ
  · intro _
    exact hP

/-- Comparison-ready ascent profile. -/
structure AscentProfile where
  shape : SixStepStructuralProfile
  family : AscentFamily
  complexity? : Option FormulaClass := none
  targetTheory? : Option FormalTheory := none

/-- Concrete paper-facing comparison profile with named stage labels. This is a
disciplined artifact object, not a formalization of the surrounding historical
arithmetic. -/
structure ConcreteComparisonProfile where
  profile : AscentProfile
  baseSystemLabel : String
  obstructionLabel : String
  blockedLabel : String
  strongerFrameworkLabel : String
  resolutionLabel : String
  licensedReimportLabel : String

/-- The mechanized DP confession viewed as a comparison-ready ascent profile. -/
def dpAsClassicalAscentProfile : AscentProfile where
  shape := dpSixStepStructuralProfile
  family := AscentFamily.reflection
  complexity? := some artsGieslLicenseProfile.complexity
  targetTheory? := some artsGieslReverseMathCalibration.target

/-- Compatibility condition for a future classical-side comparison profile. -/
def CompatibleWithDp (C : AscentProfile) : Prop :=
  StagewiseEquivalent C.shape dpSixStepStructuralProfile
    ∧ C.family = AscentFamily.reflection

@[simp] theorem dpAsClassicalAscentProfile_family :
    dpAsClassicalAscentProfile.family = AscentFamily.reflection := rfl

@[simp] theorem dpAsClassicalAscentProfile_targetTheory :
    dpAsClassicalAscentProfile.targetTheory? = some FormalTheory.RCA0_WO_omega3 := by
  simp [dpAsClassicalAscentProfile, arts_giesl_reverse_math_target]

theorem dpAsClassicalAscentProfile_compatible : CompatibleWithDp dpAsClassicalAscentProfile := by
  constructor
  · intro s
    rfl
  · rfl

/-- Named paper-facing right-hand profile for the Gödel-side comparison. The
shape is intentionally concrete and fully realized inside the artifact, while
the surrounding historical interpretation remains outside the Lean claim. -/
def godel1931PaperAscentProfile : AscentProfile where
  shape := {
    hasBaseSystem := True
    hasSelfObstruction := True
    blockedInBase := True
    hasStrongerFramework := True
    resolvedInFramework := True
    licensedReimport := True
  }
  family := AscentFamily.reflection

/-- Named stage labels for the paper-facing Gödel-side comparison object. -/
def godel1931PaperComparison : ConcreteComparisonProfile where
  profile := godel1931PaperAscentProfile
  baseSystemLabel := "PA"
  obstructionLabel := "self-referential Gödel sentence"
  blockedLabel := "base-language incompleteness"
  strongerFrameworkLabel := "external reflection / stronger metatheory"
  resolutionLabel := "truth proved at the stronger level"
  licensedReimportLabel := "externally licensed truth admission"

theorem godel1931PaperAscentProfile_realizesSixStep :
    RealizesSixStepShape godel1931PaperAscentProfile.shape := by
  simp [godel1931PaperAscentProfile, RealizesSixStepShape]

/-- Concrete theorem-backed classical-side comparison instantiation for the
paper-facing Gödel profile. -/
theorem godel1931PaperAscentProfile_compatible :
    CompatibleWithDp godel1931PaperAscentProfile := by
  rcases structural_identity with
    ⟨hBase, hSelf, hBlocked, hStronger, hResolved, hLicensed⟩
  constructor
  · intro s
    cases s with
    | baseSystem =>
        exact iff_of_true trivial hBase
    | selfObstruction =>
        exact iff_of_true trivial hSelf
    | blockedInBase =>
        exact iff_of_true trivial hBlocked
    | strongerFramework =>
        exact iff_of_true trivial hStronger
    | resolvedInFramework =>
        exact iff_of_true trivial hResolved
    | licensedReimport =>
        exact iff_of_true trivial hLicensed
  · rfl

/-- Any comparison-ready profile that matches the DP stagewise shape and keeps
reflection-family status inherits the six-step realization. -/
theorem compatibleWithDp_realizesSixStep
    (C : AscentProfile)
    (hC : CompatibleWithDp C) :
    RealizesSixStepShape C.shape := by
  exact hC.1.symm.preserves_realization structural_identity

/-- A compatible profile remains blocked in the base layer exactly when the DP
profile is blocked in the base layer. -/
theorem compatibleWithDp_blockedInBase_iff
    (C : AscentProfile)
    (hC : CompatibleWithDp C) :
    C.shape.blockedInBase ↔ dpSixStepStructuralProfile.blockedInBase :=
  hC.1 StructuralStage.blockedInBase

/-- A compatible profile resolves only at the stronger framework stage exactly
when the DP profile does. -/
theorem compatibleWithDp_resolvedInFramework_iff
    (C : AscentProfile)
    (hC : CompatibleWithDp C) :
    C.shape.resolvedInFramework ↔ dpSixStepStructuralProfile.resolvedInFramework :=
  hC.1 StructuralStage.resolvedInFramework

end OperatorKO7.ClassicalAscentProfile
