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

/-- Coarse historical base-system tag for paper-facing comparison objects. -/
inductive HistoricalBaseKind
  | peanoArithmetic
  | benchmarkContractKO7
  deriving DecidableEq, Repr

/-- Coarse historical obstruction tag. -/
inductive HistoricalObstructionKind
  | godelSentence
  | noDirectWholeWitness
  deriving DecidableEq, Repr

/-- Coarse historical stronger-framework tag. -/
inductive HistoricalFrameworkKind
  | externalReflection
  | transformedCallTransport
  deriving DecidableEq, Repr

/-- Coarse historical resolution tag. -/
inductive HistoricalResolutionKind
  | strongerTheoryTruth
  | transformedCallWitness
  deriving DecidableEq, Repr

/-- Coarse historical reimport tag. -/
inductive HistoricalReimportKind
  | licensedTruthAdmission
  | contractLicensedWitness
  deriving DecidableEq, Repr

/-- Typed historical annotation sitting above a concrete paper-facing
comparison profile. This stays deliberately coarse and artifact honest. -/
structure HistoricalComparisonAnnotation where
  baseKind : HistoricalBaseKind
  obstructionKind : HistoricalObstructionKind
  frameworkKind : HistoricalFrameworkKind
  resolutionKind : HistoricalResolutionKind
  reimportKind : HistoricalReimportKind

/-- Base-theory profile for the richer external classical comparison layer. -/
structure HistoricalBaseTheoryProfile where
  label : String
  registerApprox? : Option FormalTheory := none
  hasBaseSystem : Prop

/-- Explicit obstruction witness family for the richer external comparison
layer. -/
structure HistoricalObstructionWitness where
  label : String
  hasSelfObstruction : Prop
  blockedInBase : Prop

/-- Explicit stronger-framework operator for the richer external comparison
layer. -/
structure HistoricalFrameworkOperator where
  label : String
  frameworkAvailable : Prop
  resolvesInFramework : Prop

/-- Explicit reimport / licensed-admission map for the richer external
comparison layer. -/
structure HistoricalReimportMap where
  label : String
  licensedReimport : Prop

/-- Richer external classical comparison object.

This goes beyond labels and annotations: it packages the base-theory profile,
obstruction witness, stronger-framework operator, and reimport map together
with a concrete ascent profile and a theorem that the resulting profile is
compatible with the mechanized DP-side profile. -/
structure ExternalClassicalComparisonObject where
  baseTheory : HistoricalBaseTheoryProfile
  obstruction : HistoricalObstructionWitness
  strongerFramework : HistoricalFrameworkOperator
  reimport : HistoricalReimportMap
  family : AscentFamily
  profile : AscentProfile
  profileShape :
    profile.shape = {
      hasBaseSystem := baseTheory.hasBaseSystem
      hasSelfObstruction := obstruction.hasSelfObstruction
      blockedInBase := obstruction.blockedInBase
      hasStrongerFramework := strongerFramework.frameworkAvailable
      resolvedInFramework := strongerFramework.resolvesInFramework
      licensedReimport := reimport.licensedReimport
    }
  profileFamily : profile.family = family
  compatible :
    StagewiseEquivalent profile.shape dpSixStepStructuralProfile
      ∧ profile.family = AscentFamily.reflection

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

/-- Typed historical annotation for the paper-facing Gödel-side comparison. -/
def godel1931HistoricalAnnotation : HistoricalComparisonAnnotation where
  baseKind := HistoricalBaseKind.peanoArithmetic
  obstructionKind := HistoricalObstructionKind.godelSentence
  frameworkKind := HistoricalFrameworkKind.externalReflection
  resolutionKind := HistoricalResolutionKind.strongerTheoryTruth
  reimportKind := HistoricalReimportKind.licensedTruthAdmission

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

/-- Any richer external classical comparison object is theorem-backed at the
profile level. -/
theorem ExternalClassicalComparisonObject.supported
    (E : ExternalClassicalComparisonObject) :
    RealizesSixStepShape E.profile.shape
      ∧ E.profile.family = AscentFamily.reflection
      ∧ StagewiseEquivalent E.profile.shape dpAsClassicalAscentProfile.shape := by
  refine ⟨compatibleWithDp_realizesSixStep E.profile E.compatible, ?_, ?_⟩
  · exact E.compatible.2
  · simpa [dpAsClassicalAscentProfile] using E.compatible.1

/-- Richer base-theory profile for the paper-facing Gödel-side comparison. -/
def godel1931BaseTheoryProfile : HistoricalBaseTheoryProfile where
  label := "PA"
  hasBaseSystem := True

/-- Richer obstruction witness for the paper-facing Gödel-side comparison. -/
def godel1931ObstructionWitness : HistoricalObstructionWitness where
  label := "self-referential Gödel sentence"
  hasSelfObstruction := True
  blockedInBase := True

/-- Richer stronger-framework operator for the paper-facing Gödel-side
comparison. -/
def godel1931StrongerFrameworkOperator : HistoricalFrameworkOperator where
  label := "external reflection / stronger metatheory"
  frameworkAvailable := True
  resolvesInFramework := True

/-- Richer reimport map for the paper-facing Gödel-side comparison. -/
def godel1931ReimportMap : HistoricalReimportMap where
  label := "externally licensed truth admission"
  licensedReimport := True

/-- Richer external classical comparison object for the paper-facing
Gödel-side comparison. -/
def godel1931ExternalClassicalComparisonObject :
    ExternalClassicalComparisonObject where
  baseTheory := godel1931BaseTheoryProfile
  obstruction := godel1931ObstructionWitness
  strongerFramework := godel1931StrongerFrameworkOperator
  reimport := godel1931ReimportMap
  family := AscentFamily.reflection
  profile := godel1931PaperAscentProfile
  profileShape := rfl
  profileFamily := rfl
  compatible := godel1931PaperAscentProfile_compatible

end OperatorKO7.ClassicalAscentProfile
