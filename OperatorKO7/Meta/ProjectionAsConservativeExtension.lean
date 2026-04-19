import OperatorKO7.Meta.ClassicalAscentProfile

/-!
# Projection as Conservative Extension

Witness-language transport layer for the classical-side comparison program.

This file stays honest: it does not assert a historical theorem about Gödelian
comparison. It formalizes the exact witness-language extension shape used by the
paper's discussion and instantiates it on the benchmark contract where the
relevant transformed-call witness is already mechanized.
-/

namespace OperatorKO7.ProjectionAsConservativeExtension

open OperatorKO7.WitnessOrder
open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.ClassicalAscentProfile

private theorem iff_of_true {P Q : Prop} (hP : P) (hQ : Q) : P ↔ Q := by
  constructor
  · intro _
    exact hQ
  · intro _
    exact hP

/-- Named witness-language profile. -/
structure WitnessLanguage where
  label : String
  level : WLevel

/-- Conservative extension between witness languages on a fixed tower. -/
structure ConservativeExtension (T : WitnessTower)
    (base ext : WitnessLanguage) where
  lifts : HasWitness T base.level → HasWitness T ext.level

/-- Transport `HasWitness` along a conservative extension. -/
theorem ConservativeExtension.transports_hasWitness
    {T : WitnessTower} {base ext : WitnessLanguage}
    (hExt : ConservativeExtension T base ext)
    (hBase : HasWitness T base.level) :
    HasWitness T ext.level :=
  hExt.lifts hBase

/-- Transport `kappaLe` along a conservative extension when the target level is
at least the extension's witness level. -/
theorem ConservativeExtension.transports_kappaLe
    {T : WitnessTower} {base ext target : WitnessLanguage}
    (hExt : ConservativeExtension T base ext)
    (hLe : ext.level.toNat ≤ target.level.toNat)
    (hBase : HasWitness T base.level) :
    kappaLe T target.level := by
  exact ⟨ext.level, hLe, hExt.lifts hBase⟩

/-- Imported-whole language profile. -/
def importedWholeLanguage : WitnessLanguage where
  label := "imported whole-term"
  level := WLevel.importedWhole

/-- Transformed-call language profile. -/
def transformedCallLanguage : WitnessLanguage where
  label := "transformed call"
  level := WLevel.transformedCall

/-- On the benchmark contract tower, transformed-call witnesses are available,
so imported-whole witness claims can be conservatively re-expressed at the
transformed-call layer. This is a transport theorem, not a claim of internal
whole-term adequacy. -/
def benchmarkContractProjectionExtension :
    ConservativeExtension (contractTower ko7Tower benchmarkContract)
      importedWholeLanguage transformedCallLanguage where
  lifts := by
    intro _
    simpa [HasWitness, contractTower, transformedCallLanguage] using
      (show benchmarkContract.admissible WLevel.transformedCall
          ∧ HasWitness ko7Tower WLevel.transformedCall from
        ⟨by simp [benchmarkContract], ko7_has_transformedCall_witness⟩)

/-- Benchmark-contract instance: any imported-whole witness claim transports to
transformed-call admissibility. -/
theorem benchmarkContract_projection_extension_sound
    (hBase : HasWitness (contractTower ko7Tower benchmarkContract)
      importedWholeLanguage.level) :
    HasWitness (contractTower ko7Tower benchmarkContract)
      transformedCallLanguage.level :=
  benchmarkContractProjectionExtension.lifts hBase

/-- The benchmark contract therefore has a conservative witness-language
transport from imported-whole to transformed-call. -/
theorem benchmarkContract_projection_extension_kappaLe
    (hBase : HasWitness (contractTower ko7Tower benchmarkContract)
      importedWholeLanguage.level) :
    kappaLe (contractTower ko7Tower benchmarkContract)
      transformedCallLanguage.level := by
  exact ConservativeExtension.transports_kappaLe benchmarkContractProjectionExtension
    (by decide) hBase

/-- Concrete comparison-ready profile backed by the benchmark contract's
transformed-call witness-language transport. -/
def benchmarkTransportAscentProfile : AscentProfile where
  shape := {
    hasBaseSystem := True
    hasSelfObstruction := True
    blockedInBase := ¬ HasWitness ko7Tower WLevel.directWhole
    hasStrongerFramework := Nonempty
      (ConservativeExtension (contractTower ko7Tower benchmarkContract)
        importedWholeLanguage transformedCallLanguage)
    resolvedInFramework := kappaLe (contractTower ko7Tower benchmarkContract)
      WLevel.transformedCall
    licensedReimport := kappaLe (contractTower ko7Tower benchmarkContract)
      WLevel.transformedCall
  }
  family := AscentFamily.reflection

/-- Named benchmark-contract transport comparison object. -/
def benchmarkTransportComparison : ConcreteComparisonProfile where
  profile := benchmarkTransportAscentProfile
  baseSystemLabel := "benchmark contract over KO7"
  obstructionLabel := "contract blocks imported-whole witnesses"
  blockedLabel := "no direct whole-term witness"
  strongerFrameworkLabel := "conservative importedWhole → transformedCall transport"
  resolutionLabel := "first admissible witness at transformed-call"
  licensedReimportLabel := "transported transformed-call admission"

theorem benchmarkTransportAscentProfile_realizesSixStep :
    RealizesSixStepShape benchmarkTransportAscentProfile.shape := by
  refine ⟨trivial, trivial, ?_, ?_, ?_, ?_⟩
  · exact ko7_no_directWhole_witness
  · exact ⟨benchmarkContractProjectionExtension⟩
  · exact ko7_kappaContract_le_transformedCall
  · exact ko7_kappaContract_le_transformedCall

/-- The benchmark-contract conservative-extension layer now directly yields a
concrete comparison profile, not only an abstract transport theorem. -/
theorem benchmarkContractProjectionExtension_instantiates_concreteComparison :
    RealizesSixStepShape benchmarkTransportAscentProfile.shape
      ∧ benchmarkTransportAscentProfile.family = AscentFamily.reflection := by
  exact ⟨benchmarkTransportAscentProfile_realizesSixStep, rfl⟩

/-- Concrete theorem-backed transport-side profile instantiation compatible with
the mechanized DP ascent profile. -/
theorem benchmarkTransportAscentProfile_compatible :
    CompatibleWithDp benchmarkTransportAscentProfile := by
  rcases OperatorKO7.ProofTheoreticRegister.structural_identity with
    ⟨hBase, hSelf, hBlocked, hStronger, hResolved, hLicensed⟩
  constructor
  · intro s
    cases s with
    | baseSystem =>
        exact iff_of_true trivial hBase
    | selfObstruction =>
        exact iff_of_true trivial hSelf
    | blockedInBase =>
        exact iff_of_true ko7_no_directWhole_witness hBlocked
    | strongerFramework =>
        exact iff_of_true ⟨benchmarkContractProjectionExtension⟩ hStronger
    | resolvedInFramework =>
        exact iff_of_true ko7_kappaContract_le_transformedCall hResolved
    | licensedReimport =>
        exact iff_of_true ko7_kappaContract_le_transformedCall hLicensed
  · rfl

end OperatorKO7.ProjectionAsConservativeExtension
