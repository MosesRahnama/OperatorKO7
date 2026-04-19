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

/-- Comparison-ready ascent profile. -/
structure AscentProfile where
  shape : SixStepStructuralProfile
  family : AscentFamily
  complexity? : Option FormulaClass := none
  targetTheory? : Option FormalTheory := none

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
