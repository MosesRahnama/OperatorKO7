import OperatorKO7.Meta.ClassicalAscentProfile
import OperatorKO7.Meta.ProjectionAsConservativeExtension

/-!
# Structural Identity Comparison

Comparison theorems for ascent profiles that are stagewise equivalent to the
mechanized DP-side six-step profile.

This does not introduce a new historical theorem. It formalizes the exact shape
of the stronger comparison claim so that any future classical-side profile can
be plugged into a machine-checked comparison object.
-/

namespace OperatorKO7.StructuralIdentityComparison

open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.ReflectionSchema
open OperatorKO7.ClassicalAscentProfile
open OperatorKO7.ProjectionAsConservativeExtension

/-- Comparison object between two ascent profiles. -/
structure ComparisonWitness
    (left right : AscentProfile) where
  sameFamily : left.family = right.family
  sameShape : StagewiseEquivalent left.shape right.shape

/-- Packaged concrete comparison object: a named right-hand profile together
with its explicit comparison witness against the mechanized DP profile. -/
structure HistoricalComparisonObject where
  concrete : ConcreteComparisonProfile
  comparison : ComparisonWitness concrete.profile dpAsClassicalAscentProfile

/-- Stronger packaged comparison object carrying a typed historical annotation
above the concrete comparison profile and its theorem-backed witness. -/
structure AnnotatedHistoricalComparisonObject where
  annotation : HistoricalComparisonAnnotation
  historical : HistoricalComparisonObject

/-- Concrete theorem-bearing historical comparison object.

This is stronger than the earlier annotation-only wrapper: it packages the
named comparison profile together with

- an explicit stagewise realization witness, and
- the theorem-backed comparison witness against the mechanized DP profile.

This is the repository's concrete right-hand historical object, as opposed to a
purely abstract comparison schema. -/
structure GroundedHistoricalComparisonObject where
  annotation : HistoricalComparisonAnnotation
  concrete : ConcreteComparisonProfile
  realization : StagewiseRealization concrete.profile.shape
  comparison : ComparisonWitness concrete.profile dpAsClassicalAscentProfile

/-- Convert a richer external classical comparison object into the grounded
historical comparison interface. -/
def ExternalClassicalComparisonObject.toGroundedHistoricalComparisonObject
    (annotation : HistoricalComparisonAnnotation)
    (baseLabel obstructionLabel frameworkLabel resolutionLabel reimportLabel : String)
    (E : ExternalClassicalComparisonObject) :
    GroundedHistoricalComparisonObject where
  annotation := annotation
  concrete := {
    profile := E.profile
    baseSystemLabel := baseLabel
    obstructionLabel := obstructionLabel
    blockedLabel := obstructionLabel
    strongerFrameworkLabel := frameworkLabel
    resolutionLabel := resolutionLabel
    licensedReimportLabel := reimportLabel
  }
  realization := by
    rcases (realizesSixStepShape_iff_stagewise E.profile.shape).1
      (compatibleWithDp_realizesSixStep E.profile E.compatible) with ⟨hR⟩
    exact hR
  comparison := {
    sameFamily := by simpa [dpAsClassicalAscentProfile] using E.compatible.2
    sameShape := by simpa [dpAsClassicalAscentProfile] using E.compatible.1
  }

/-- Structural-identity comparison preserves six-step realization from left to
right. -/
theorem ComparisonWitness.right_realizes
    {left right : AscentProfile}
    (C : ComparisonWitness left right)
    (hLeft : RealizesSixStepShape left.shape) :
    RealizesSixStepShape right.shape :=
  C.sameShape.preserves_realization hLeft

/-- And symmetrically from right to left. -/
theorem ComparisonWitness.left_realizes
    {left right : AscentProfile}
    (C : ComparisonWitness left right)
    (hRight : RealizesSixStepShape right.shape) :
    RealizesSixStepShape left.shape := by
  apply C.sameShape.symm.preserves_realization
  exact hRight

/-- Any comparison-ready reflection profile compatible with the DP profile has
an explicit structural-identity comparison against the mechanized DP ascent
profile. -/
def comparisonAgainstDp
    (C : AscentProfile)
    (hC : CompatibleWithDp C) :
    ComparisonWitness C dpAsClassicalAscentProfile where
  sameFamily := by simpa [dpAsClassicalAscentProfile] using hC.2
  sameShape := by simpa [dpAsClassicalAscentProfile] using hC.1

/-- Main reusable comparison theorem: any future classical reflection profile
that matches the DP stagewise shape is structurally identical to the mechanized
DP profile at the level of the six-step comparison schema. -/
theorem compatible_profile_has_dp_structural_identity
    (C : AscentProfile)
    (hC : CompatibleWithDp C) :
    RealizesSixStepShape C.shape
      ∧ C.family = dpAsClassicalAscentProfile.family
      ∧ StagewiseEquivalent C.shape dpAsClassicalAscentProfile.shape := by
  refine ⟨compatibleWithDp_realizesSixStep C hC, ?_, ?_⟩
  · simpa [dpAsClassicalAscentProfile] using hC.2
  · simpa [dpAsClassicalAscentProfile] using hC.1

/-- The mechanized DP profile is structurally identical to itself in the new
comparison sense. -/
def dpStructuralIdentitySelfComparison :
    ComparisonWitness dpAsClassicalAscentProfile dpAsClassicalAscentProfile where
  sameFamily := rfl
  sameShape := by intro s; rfl

/-- Concrete comparison witness instantiating the right-hand profile with the
named paper-facing Gödel-side object. -/
def godel1931PaperComparisonAgainstDp :
    ComparisonWitness godel1931PaperAscentProfile dpAsClassicalAscentProfile :=
  comparisonAgainstDp godel1931PaperAscentProfile
    godel1931PaperAscentProfile_compatible

/-- Concrete theorem-backed structural identity for the named paper-facing
Gödel-side comparison object. -/
theorem godel1931Paper_has_dp_structural_identity :
    RealizesSixStepShape godel1931PaperAscentProfile.shape
      ∧ godel1931PaperAscentProfile.family = dpAsClassicalAscentProfile.family
      ∧ StagewiseEquivalent godel1931PaperAscentProfile.shape
          dpAsClassicalAscentProfile.shape := by
  exact compatible_profile_has_dp_structural_identity
    godel1931PaperAscentProfile godel1931PaperAscentProfile_compatible

/-- Concrete comparison witness instantiating the right-hand profile with the
benchmark conservative-extension transport object. -/
def benchmarkTransportComparisonAgainstDp :
    ComparisonWitness benchmarkTransportAscentProfile dpAsClassicalAscentProfile :=
  comparisonAgainstDp benchmarkTransportAscentProfile
    benchmarkTransportAscentProfile_compatible

/-- Concrete theorem-backed structural identity for the benchmark transport
comparison profile. This is the direct link from the conservative-extension
layer to the six-step comparison layer. -/
theorem benchmarkTransport_has_dp_structural_identity :
    RealizesSixStepShape benchmarkTransportAscentProfile.shape
      ∧ benchmarkTransportAscentProfile.family = dpAsClassicalAscentProfile.family
      ∧ StagewiseEquivalent benchmarkTransportAscentProfile.shape
          dpAsClassicalAscentProfile.shape := by
  exact compatible_profile_has_dp_structural_identity
    benchmarkTransportAscentProfile benchmarkTransportAscentProfile_compatible

/-- Any packaged concrete comparison object inherits a theorem-backed
structural-identity statement against the mechanized DP profile. -/
theorem HistoricalComparisonObject.supported
    (H : HistoricalComparisonObject) :
    RealizesSixStepShape H.concrete.profile.shape
      ∧ H.concrete.profile.family = dpAsClassicalAscentProfile.family
      ∧ StagewiseEquivalent H.concrete.profile.shape
          dpAsClassicalAscentProfile.shape := by
  refine ⟨H.comparison.left_realizes structural_identity, ?_, ?_⟩
  · exact H.comparison.sameFamily
  · exact H.comparison.sameShape

/-- Any grounded historical comparison object is theorem-backed both as a
six-step realization and as a structural comparison against the mechanized DP
profile. -/
theorem GroundedHistoricalComparisonObject.supported
    (H : GroundedHistoricalComparisonObject) :
    RealizesSixStepShape H.concrete.profile.shape
      ∧ H.concrete.profile.family = dpAsClassicalAscentProfile.family
      ∧ StagewiseEquivalent H.concrete.profile.shape
          dpAsClassicalAscentProfile.shape := by
  refine ⟨?_, H.comparison.sameFamily, H.comparison.sameShape⟩
  exact (realizesSixStepShape_iff_stagewise H.concrete.profile.shape).2 ⟨H.realization⟩

/-- Forget the explicit theorem witness and recover the lighter historical
comparison object. -/
def GroundedHistoricalComparisonObject.toHistoricalComparisonObject
    (H : GroundedHistoricalComparisonObject) :
    HistoricalComparisonObject where
  concrete := H.concrete
  comparison := H.comparison

/-- Forget the explicit theorem witness and recover the lighter annotated
historical comparison object. -/
def GroundedHistoricalComparisonObject.toAnnotatedHistoricalComparisonObject
    (H : GroundedHistoricalComparisonObject) :
    AnnotatedHistoricalComparisonObject where
  annotation := H.annotation
  historical := H.toHistoricalComparisonObject

/-- Packaged paper-facing Gödel-side comparison object. -/
def godel1931HistoricalComparisonObject : HistoricalComparisonObject where
  concrete := godel1931PaperComparison
  comparison := godel1931PaperComparisonAgainstDp

/-- Packaged benchmark-transport comparison object. -/
def benchmarkTransportHistoricalComparisonObject : HistoricalComparisonObject where
  concrete := benchmarkTransportComparison
  comparison := benchmarkTransportComparisonAgainstDp

/-- Theorem-bearing Gödel-side historical comparison object. -/
def godel1931GroundedHistoricalComparisonObject :
    GroundedHistoricalComparisonObject where
  annotation := godel1931HistoricalAnnotation
  concrete := godel1931PaperComparison
  realization := by
    rcases
      (realizesSixStepShape_iff_stagewise godel1931PaperAscentProfile.shape).1
        godel1931PaperAscentProfile_realizesSixStep with
      ⟨hR⟩
    exact hR
  comparison := godel1931PaperComparisonAgainstDp

/-- The richer external Gödel-side comparison object induces the grounded
historical comparison interface. -/
def godel1931ExternalGroundedHistoricalComparisonObject :
    GroundedHistoricalComparisonObject :=
  ExternalClassicalComparisonObject.toGroundedHistoricalComparisonObject
    godel1931HistoricalAnnotation
    godel1931BaseTheoryProfile.label
    godel1931ObstructionWitness.label
    godel1931StrongerFrameworkOperator.label
    "truth proved at the stronger level"
    godel1931ReimportMap.label
    godel1931ExternalClassicalComparisonObject

/-- Richer base-theory profile for the benchmark transport comparison. -/
def benchmarkTransportBaseTheoryProfile : HistoricalBaseTheoryProfile where
  label := "benchmark contract over KO7"
  registerApprox? := some FormalTheory.RCA0_WO_omega3
  hasBaseSystem := True

/-- Richer obstruction witness for the benchmark transport comparison. -/
def benchmarkTransportObstructionWitness : HistoricalObstructionWitness where
  label := "no direct whole-term witness"
  hasSelfObstruction := True
  blockedInBase := ¬ OperatorKO7.WitnessOrder.HasWitness
    OperatorKO7.WitnessOrder.ko7Tower
    OperatorKO7.WitnessOrder.WLevel.directWhole

/-- Richer stronger-framework operator for the benchmark transport comparison. -/
def benchmarkTransportFrameworkOperator : HistoricalFrameworkOperator where
  label := "conservative importedWhole → transformedCall transport"
  frameworkAvailable := Nonempty
    (ConservativeExtension
      (OperatorKO7.WitnessOrder.contractTower
        OperatorKO7.WitnessOrder.ko7Tower
        OperatorKO7.WitnessOrder.benchmarkContract)
      importedWholeLanguage transformedCallLanguage)
  resolvesInFramework :=
    OperatorKO7.WitnessOrder.kappaLe
      (OperatorKO7.WitnessOrder.contractTower
        OperatorKO7.WitnessOrder.ko7Tower
        OperatorKO7.WitnessOrder.benchmarkContract)
      OperatorKO7.WitnessOrder.WLevel.transformedCall

/-- Richer reimport map for the benchmark transport comparison. -/
def benchmarkTransportReimportMap : HistoricalReimportMap where
  label := "transported transformed-call admission"
  licensedReimport :=
    OperatorKO7.WitnessOrder.kappaLe
      (OperatorKO7.WitnessOrder.contractTower
        OperatorKO7.WitnessOrder.ko7Tower
        OperatorKO7.WitnessOrder.benchmarkContract)
      OperatorKO7.WitnessOrder.WLevel.transformedCall

/-- Richer external classical comparison object for the benchmark transport
layer. -/
def benchmarkTransportExternalClassicalComparisonObject :
    ExternalClassicalComparisonObject where
  baseTheory := benchmarkTransportBaseTheoryProfile
  obstruction := benchmarkTransportObstructionWitness
  strongerFramework := benchmarkTransportFrameworkOperator
  reimport := benchmarkTransportReimportMap
  family := AscentFamily.reflection
  profile := benchmarkTransportAscentProfile
  profileShape := rfl
  profileFamily := rfl
  compatible := benchmarkTransportAscentProfile_compatible

/-- Theorem-bearing benchmark-transport historical comparison object. -/
def benchmarkTransportGroundedHistoricalComparisonObject :
    GroundedHistoricalComparisonObject where
  annotation := benchmarkTransportHistoricalAnnotation
  concrete := benchmarkTransportComparison
  realization := by
    rcases
      (realizesSixStepShape_iff_stagewise benchmarkTransportAscentProfile.shape).1
        benchmarkTransportAscentProfile_realizesSixStep with
      ⟨hR⟩
    exact hR
  comparison := benchmarkTransportComparisonAgainstDp

/-- The richer external benchmark-transport comparison object induces the
grounded historical comparison interface. -/
def benchmarkTransportExternalGroundedHistoricalComparisonObject :
    GroundedHistoricalComparisonObject :=
  ExternalClassicalComparisonObject.toGroundedHistoricalComparisonObject
    benchmarkTransportHistoricalAnnotation
    benchmarkTransportBaseTheoryProfile.label
    benchmarkTransportObstructionWitness.label
    benchmarkTransportFrameworkOperator.label
    "first admissible witness at transformed-call"
    benchmarkTransportReimportMap.label
    benchmarkTransportExternalClassicalComparisonObject

/-- Typed Gödel-side historical comparison object. -/
def godel1931AnnotatedHistoricalComparisonObject :
    AnnotatedHistoricalComparisonObject where
  annotation := godel1931HistoricalAnnotation
  historical := godel1931HistoricalComparisonObject

/-- Typed benchmark-transport historical comparison object. -/
def benchmarkTransportAnnotatedHistoricalComparisonObject :
    AnnotatedHistoricalComparisonObject where
  annotation := benchmarkTransportHistoricalAnnotation
  historical := benchmarkTransportHistoricalComparisonObject

/-- Supported form of the paper-facing Gödel-side comparison object. -/
theorem godel1931HistoricalComparison_supported :
    RealizesSixStepShape godel1931HistoricalComparisonObject.concrete.profile.shape
      ∧ godel1931HistoricalComparisonObject.concrete.profile.family =
          dpAsClassicalAscentProfile.family
      ∧ StagewiseEquivalent
          godel1931HistoricalComparisonObject.concrete.profile.shape
          dpAsClassicalAscentProfile.shape := by
  exact godel1931HistoricalComparisonObject.supported

/-- Supported form of the benchmark-transport comparison object. -/
theorem benchmarkTransportHistoricalComparison_supported :
    RealizesSixStepShape
        benchmarkTransportHistoricalComparisonObject.concrete.profile.shape
      ∧ benchmarkTransportHistoricalComparisonObject.concrete.profile.family =
          dpAsClassicalAscentProfile.family
      ∧ StagewiseEquivalent
          benchmarkTransportHistoricalComparisonObject.concrete.profile.shape
          dpAsClassicalAscentProfile.shape := by
  exact benchmarkTransportHistoricalComparisonObject.supported

/-- Supported form of the theorem-bearing Gödel-side historical comparison
object. -/
theorem godel1931GroundedHistoricalComparison_supported :
    RealizesSixStepShape
        godel1931GroundedHistoricalComparisonObject.concrete.profile.shape
      ∧ godel1931GroundedHistoricalComparisonObject.concrete.profile.family =
          dpAsClassicalAscentProfile.family
      ∧ StagewiseEquivalent
          godel1931GroundedHistoricalComparisonObject.concrete.profile.shape
          dpAsClassicalAscentProfile.shape := by
  exact godel1931GroundedHistoricalComparisonObject.supported

/-- Supported form of the richer external Gödel-side comparison object. -/
theorem godel1931ExternalClassicalComparison_supported :
    RealizesSixStepShape godel1931ExternalClassicalComparisonObject.profile.shape
      ∧ godel1931ExternalClassicalComparisonObject.profile.family =
          dpAsClassicalAscentProfile.family
      ∧ StagewiseEquivalent godel1931ExternalClassicalComparisonObject.profile.shape
          dpAsClassicalAscentProfile.shape := by
  exact godel1931ExternalClassicalComparisonObject.supported

/-- The richer external Gödel-side object recovers the grounded interface. -/
theorem godel1931ExternalGroundedHistoricalComparison_supported :
    RealizesSixStepShape
        godel1931ExternalGroundedHistoricalComparisonObject.concrete.profile.shape
      ∧ godel1931ExternalGroundedHistoricalComparisonObject.concrete.profile.family =
          dpAsClassicalAscentProfile.family
      ∧ StagewiseEquivalent
          godel1931ExternalGroundedHistoricalComparisonObject.concrete.profile.shape
          dpAsClassicalAscentProfile.shape := by
  exact godel1931ExternalGroundedHistoricalComparisonObject.supported

/-- Supported form of the theorem-bearing benchmark-transport historical
comparison object. -/
theorem benchmarkTransportGroundedHistoricalComparison_supported :
    RealizesSixStepShape
        benchmarkTransportGroundedHistoricalComparisonObject.concrete.profile.shape
      ∧ benchmarkTransportGroundedHistoricalComparisonObject.concrete.profile.family =
          dpAsClassicalAscentProfile.family
      ∧ StagewiseEquivalent
          benchmarkTransportGroundedHistoricalComparisonObject.concrete.profile.shape
          dpAsClassicalAscentProfile.shape := by
  exact benchmarkTransportGroundedHistoricalComparisonObject.supported

/-- Supported form of the richer external benchmark-transport comparison
object. -/
theorem benchmarkTransportExternalClassicalComparison_supported :
    RealizesSixStepShape benchmarkTransportExternalClassicalComparisonObject.profile.shape
      ∧ benchmarkTransportExternalClassicalComparisonObject.profile.family =
          dpAsClassicalAscentProfile.family
      ∧ StagewiseEquivalent
          benchmarkTransportExternalClassicalComparisonObject.profile.shape
          dpAsClassicalAscentProfile.shape := by
  exact benchmarkTransportExternalClassicalComparisonObject.supported

/-- The richer external benchmark-transport object recovers the grounded
interface. -/
theorem benchmarkTransportExternalGroundedHistoricalComparison_supported :
    RealizesSixStepShape
        benchmarkTransportExternalGroundedHistoricalComparisonObject.concrete.profile.shape
      ∧ benchmarkTransportExternalGroundedHistoricalComparisonObject.concrete.profile.family =
          dpAsClassicalAscentProfile.family
      ∧ StagewiseEquivalent
          benchmarkTransportExternalGroundedHistoricalComparisonObject.concrete.profile.shape
          dpAsClassicalAscentProfile.shape := by
  exact benchmarkTransportExternalGroundedHistoricalComparisonObject.supported

/-- Typed Gödel-side historical comparison object remains theorem-backed. -/
theorem godel1931AnnotatedHistoricalComparison_supported :
    RealizesSixStepShape
        godel1931AnnotatedHistoricalComparisonObject.historical.concrete.profile.shape
      ∧ godel1931AnnotatedHistoricalComparisonObject.historical.concrete.profile.family =
          dpAsClassicalAscentProfile.family
      ∧ StagewiseEquivalent
          godel1931AnnotatedHistoricalComparisonObject.historical.concrete.profile.shape
          dpAsClassicalAscentProfile.shape := by
  exact godel1931AnnotatedHistoricalComparisonObject.historical.supported

/-- Typed benchmark-transport historical comparison object remains
theorem-backed. -/
theorem benchmarkTransportAnnotatedHistoricalComparison_supported :
    RealizesSixStepShape
        benchmarkTransportAnnotatedHistoricalComparisonObject.historical.concrete.profile.shape
      ∧ benchmarkTransportAnnotatedHistoricalComparisonObject.historical.concrete.profile.family =
          dpAsClassicalAscentProfile.family
      ∧ StagewiseEquivalent
          benchmarkTransportAnnotatedHistoricalComparisonObject.historical.concrete.profile.shape
          dpAsClassicalAscentProfile.shape := by
  exact benchmarkTransportAnnotatedHistoricalComparisonObject.historical.supported

end OperatorKO7.StructuralIdentityComparison
