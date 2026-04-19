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

end OperatorKO7.StructuralIdentityComparison
