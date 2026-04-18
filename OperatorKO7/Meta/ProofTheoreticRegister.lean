import OperatorKO7.Meta.WitnessOrder
import OperatorKO7.Meta.OperationalIncompleteness
import OperatorKO7.Meta.ConfessionMethod_DP
import OperatorKO7.Meta.ConfessionMethod_Unification
import OperatorKO7.Meta.DependencyPairs_Works
import OperatorKO7.Meta.SchemaConfessionDominance
import Mathlib.Tactic

/-!
# Proof-Theoretic Register for the Failure-Floor Paper

This module formalizes the remaining proof-theoretic bookkeeping layer used in
Paper 2:

- the six-step ascent profile behind the structural-identity discussion;
- the diagonal-vs-reflection taxonomy used to classify the DP confession;
- the `Π⁰₂` / `IΣ₁` / fixed-finite-`PRA` register for the Arts--Giesl license;
- the conjectural reverse-mathematical target as a named statement object;
- the constant-overhead recursor-side license bound.

The intent is to mechanize the artifact-facing content of the paper's
proof-theoretic claims without pretending to formalize the surrounding history
of Gödelian incompleteness inside this repository.
-/

namespace OperatorKO7.ProofTheoreticRegister

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.WitnessOrder
open OperatorKO7.MetaOperationalIncompleteness
open OperatorKO7.ConfessionMethodFamily
open OperatorKO7.MetaDependencyPairs
open OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem

/-- Coarse proof-theoretic family used in the paper's taxonomy. -/
inductive AscentFamily
  | diagonal
  | reflection
  deriving DecidableEq, Repr

/-- Coarse arithmetical class used for paper-facing license bookkeeping. -/
inductive FormulaClass
  | pi02
  deriving DecidableEq, Repr

/-- Coarse formal-theory register used in the paper's proof-theoretic notes. -/
inductive FormalTheory
  | PRA
  | ISigma1
  | RCA0
  | RCA0_WO_omega3
  | WO_epsilon0
  deriving DecidableEq, Repr

namespace FormalTheory

/-- An explicit coarse ordering for the proof-theoretic register. -/
def toNat : FormalTheory → Nat
  | PRA => 0
  | ISigma1 => 1
  | RCA0 => 2
  | RCA0_WO_omega3 => 3
  | WO_epsilon0 => 4

instance : LE FormalTheory := ⟨fun a b => a.toNat ≤ b.toNat⟩
instance : LT FormalTheory := ⟨fun a b => a.toNat < b.toNat⟩

instance (a b : FormalTheory) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toNat ≤ b.toNat))

instance (a b : FormalTheory) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toNat < b.toNat))

end FormalTheory

/-- Artifact-side six-step structural profile for a confession-style ascent. -/
structure SixStepStructuralProfile where
  hasBaseSystem : Prop
  hasSelfObstruction : Prop
  blockedInBase : Prop
  hasStrongerFramework : Prop
  resolvedInFramework : Prop
  licensedReimport : Prop

/-- Realization predicate for the six-step profile. -/
def RealizesSixStepShape (P : SixStepStructuralProfile) : Prop :=
  P.hasBaseSystem
    ∧ P.hasSelfObstruction
    ∧ P.blockedInBase
    ∧ P.hasStrongerFramework
    ∧ P.resolvedInFramework
    ∧ P.licensedReimport

/-- The step-duplicating DP confession viewed through the six-step shape used in
Paper 2's structural-identity discussion. -/
def dpSixStepStructuralProfile : SixStepStructuralProfile where
  hasBaseSystem := True
  hasSelfObstruction :=
    ∃ b s n : Trace, Step (recΔ b s (delta n)) (app s (recΔ b s n))
  blockedInBase := ¬ HasWitness ko7Tower WLevel.directWhole
  hasStrongerFramework :=
    ∃ C : ConfessionMethod OperatorKO7.CompositionalImpossibility.ko7Schema,
      C.license = SoundnessLicense.artsGiesl2000
  resolvedInFramework := HasWitness ko7Tower WLevel.transformedCall
  licensedReimport :=
    ∃ fw : CertifiedForgettingWitness,
      fw = CertifiedForgettingWitness.ofConfessionMethod dpConfession

/-- Paper 2 Theorem 5.11, artifact-facing mechanized form: the dependency-pair
confession on the duplicator realizes the full six-step ascent profile. -/
theorem structural_identity :
    RealizesSixStepShape dpSixStepStructuralProfile := by
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨Trace.void, Trace.void, Trace.void, ?_⟩
    simpa using (rec_succ_extracts_dependency_pair Trace.void Trace.void Trace.void).1
  · exact ko7_no_directWhole_witness
  · exact ⟨dpConfession, rfl⟩
  · exact ko7_has_transformedCall_witness
  · exact ⟨CertifiedForgettingWitness.ofConfessionMethod dpConfession, rfl⟩

/-- Reflection-family evidence: the base layer is blocked, the transformed
problem is resolved only after admitting an external license, and the admitted
license is tracked together with its proof-theoretic class. -/
structure ReflectionFamilyEvidence where
  blockedInBase : Prop
  externalLicense : SoundnessLicense
  transformedResolution : Prop
  conservativeClass : FormulaClass

/-- Diagonal-family evidence would require an internal coding/evaluation
interface and a contradiction-producing fixed-point-free move. We keep the
interface abstract because the paper's claim is only that the DP confession does
not enter through this route. -/
structure DiagonalFamilyEvidence where
  hasInternalCodeObject : Prop
  hasEvaluationMap : Prop
  contradictionDriven : Prop

/-- Proof-theoretic classification object. -/
inductive AscentFamilyEvidence
  | diagonal (d : DiagonalFamilyEvidence)
  | reflection (r : ReflectionFamilyEvidence)

/-- The dependency-pair confession is classified by the reflection-family
register. -/
def dpReflectionEvidence : ReflectionFamilyEvidence where
  blockedInBase := dpSixStepStructuralProfile.blockedInBase
  externalLicense := SoundnessLicense.artsGiesl2000
  transformedResolution := dpSixStepStructuralProfile.resolvedInFramework
  conservativeClass := FormulaClass.pi02

/-- The proof-theoretic register attached to the DP confession. -/
def dpProofTheoreticRegister : AscentFamilyEvidence :=
  .reflection dpReflectionEvidence

/-- Paper 2 Proposition 5.12, mechanized taxonomy form: the DP confession is
not classified by the Lawvere--Yanofsky diagonal branch. -/
theorem dp_confession_not_lawvere_yanofsky_diagonal :
    ¬ ∃ d, dpProofTheoreticRegister = .diagonal d := by
  intro h
  rcases h with ⟨d, hd⟩
  cases hd

/-- Paper 2 Proposition 5.13, mechanized taxonomy form: the DP confession is a
reflection-family ascent. -/
theorem dp_confession_is_reflection_family_ascent :
    ∃ r, dpProofTheoreticRegister = .reflection r := by
  exact ⟨dpReflectionEvidence, rfl⟩

/-- Paper-facing profile of the Arts--Giesl soundness license. -/
structure SoundnessLicenseProfile where
  family : AscentFamily
  complexity : FormulaClass
  formalizableIn : FormalTheory
  fixedFiniteProvableIn : FormalTheory

/-- The Arts--Giesl soundness license as tracked in the paper's proof-theoretic
register. -/
def artsGieslLicenseProfile : SoundnessLicenseProfile where
  family := AscentFamily.reflection
  complexity := FormulaClass.pi02
  formalizableIn := FormalTheory.ISigma1
  fixedFiniteProvableIn := FormalTheory.PRA

/-- Paper 2 Proposition 5.14: the Arts--Giesl license is tracked at `Π⁰₂`
complexity. -/
@[simp] theorem arts_giesl_soundness_is_pi02 :
    artsGieslLicenseProfile.complexity = FormulaClass.pi02 := rfl

/-- Paper 2 Proposition 5.14: the Arts--Giesl license is tracked as
formalizable in `IΣ₁`. -/
@[simp] theorem arts_giesl_formalizable_in_ISigma1 :
    artsGieslLicenseProfile.formalizableIn = FormalTheory.ISigma1 := rfl

/-- Paper 2 Proposition 5.14: for each fixed finite TRS, the same register is
tracked down at `PRA`. -/
@[simp] theorem arts_giesl_fixed_finite_TRS_in_PRA :
    artsGieslLicenseProfile.fixedFiniteProvableIn = FormalTheory.PRA := rfl

/-- Conjectural reverse-mathematical calibration target for the Arts--Giesl
license. This is a formalized statement object, not a proved theorem. -/
structure ReverseMathConjecture where
  target : FormalTheory
  upperBenchmark : FormalTheory
  targetBelowUpper : target < upperBenchmark

/-- Paper 2 Conjecture 5.15 as a named target object. -/
def artsGieslReverseMathCalibration : ReverseMathConjecture where
  target := FormalTheory.RCA0_WO_omega3
  upperBenchmark := FormalTheory.WO_epsilon0
  targetBelowUpper := by decide

@[simp] theorem arts_giesl_reverse_math_target :
    artsGieslReverseMathCalibration.target = FormalTheory.RCA0_WO_omega3 := rfl

@[simp] theorem arts_giesl_reverse_math_target_below_epsilon0 :
    artsGieslReverseMathCalibration.target < artsGieslReverseMathCalibration.upperBenchmark :=
  artsGieslReverseMathCalibration.targetBelowUpper

/-! ## Constant-overhead recursor-side AG bound -/

/-- Rule count of the primitive duplicator. -/
def recursorRuleCount : Nat := 2

/-- Signature size used by the paper's recursor-side bound. -/
def recursorSignatureSize : Nat := 4

/-- The extracted dependency-pair count for the primitive duplicator. -/
def recursorDependencyPairCount : Nat := 1

/-- Paper-facing construction cost envelope for the DP graph. -/
def agGraphConstructionCost : Nat :=
  recursorRuleCount ^ 2 * recursorSignatureSize

/-- Paper-facing base-order check cost on the single extracted pair. -/
def agBaseOrderCost : Nat :=
  recursorDependencyPairCount

/-- Constant schematic overhead of one Arts--Giesl soundness invocation in the
paper-facing cost model. -/
def agSchematicInvocationCost : Nat := 1

/-- Total constant license overhead on the primitive duplicator. -/
def agLicenseOverhead : Nat :=
  agGraphConstructionCost + agBaseOrderCost + agSchematicInvocationCost

@[simp] theorem ag_license_overhead_eq : agLicenseOverhead = 18 := by
  decide

/-- The transformed-call residual proof work on the primitive duplicator is
linear in the counter height, with constant license overhead. -/
theorem ag_proof_length_on_step_duplicating_recursor (K : Nat) :
    residualProofWork K + agLicenseOverhead = K + agLicenseOverhead := by
  simp [residualProofWork, agLicenseOverhead]

end OperatorKO7.ProofTheoreticRegister
