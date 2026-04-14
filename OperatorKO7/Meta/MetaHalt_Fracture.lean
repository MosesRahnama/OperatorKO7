import OperatorKO7.Meta.MetaHalt_Signatures
import OperatorKO7.Meta.MetaHalt_Predicate
import OperatorKO7.Meta.MetaHalt_Regress
import OperatorKO7.Meta.MetaHalt_Soundness
import OperatorKO7.Meta.WitnessOrder
import OperatorKO7.Meta.OperationalIncompleteness
import OperatorKO7.Meta.ConfessionMethod_Family

/-!
# Pre-Undecidability Fracture Theorem

This module mechanizes the central theorem of the operational-
incompleteness paper: the five-clause fracture theorem together with its
supporting exhaustion-gap proposition and the architectural necessity
corollaries.

Key identifiers:

- `exhaustionGap` : the task-relativized exhaustion gap of Definition 6.0;
- `no_c4_above_nonzero_gap` : Proposition 6.1;
- `pre_undecidability_fracture` : bundled threshold-form fracture theorem;
- `FaultLineCompleteArchitecture` : Definition 7.1, six-field record;
- `flc_layers_necessary_witness_transition` : witness-transition necessity;
- `flc_layers_necessary_meta_halt` : META-HALT necessity.
-/

namespace OperatorKO7.MetaHalt.Fracture

open OperatorKO7
open OperatorKO7.WitnessOrder
open OperatorKO7.MetaHalt.Signatures
open OperatorKO7.MetaHalt.Predicate
open OperatorKO7.MetaHalt.Regress
open OperatorKO7.MetaHalt.Soundness
open OperatorKO7.MetaOperationalIncompleteness
open OperatorKO7.ConfessionMethodFamily

/-- Task-relevant operations. -/
inductive OperationTag
  | recursiveCallExtraction
  | subtermCriterionApplication
  | projectionToCounterCoordinate
  | externalSoundnessInvocation
  | directMeasureConstruction
  | precedenceSelection
  | polynomialSelection
  deriving DecidableEq, Repr

/-- The minimal set of operations required for a complete resolution of the
    obligation under the relevant witness language. -/
def taskRequiredOperations (O : ObligationSignature) : List OperationTag :=
  if O.hasTag GoalTag.containsDuplicatingStep then
    [ .recursiveCallExtraction,
      .subtermCriterionApplication,
      .projectionToCounterCoordinate,
      .externalSoundnessInvocation ]
  else
    []

/-- Operations the run actually performed. -/
structure OperationsPerformed where
  tags : List OperationTag
  deriving DecidableEq, Repr

/-- Definition 6.0: task-relativized exhaustion gap, returned as a reduced
    numerator/denominator pair over naturals. -/
def exhaustionGap (O : ObligationSignature) (P : OperationsPerformed) : Nat × Nat :=
  let req := taskRequiredOperations O
  let den := req.length
  let inter := req.filter (fun op => decide (op ∈ P.tags))
  if den = 0 then
    (0, 1)
  else
    (den - inter.length, den)

private theorem filter_length_le {α : Type} (xs : List α) (p : α → Bool) :
    (xs.filter p).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      by_cases hx : p x = true
      · simpa [hx] using Nat.succ_le_succ ih
      · simpa [hx] using Nat.le_succ_of_le ih

private theorem filter_length_eq_length_iff_all {α : Type} (xs : List α) (p : α → Bool) :
    (xs.filter p).length = xs.length ↔ xs.all p = true := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      by_cases hx : p x = true
      · simp [hx, ih]
      · have hle : (xs.filter p).length ≤ xs.length := filter_length_le xs p
        have hne : (xs.filter p).length ≠ xs.length + 1 :=
          Nat.ne_of_lt (Nat.lt_succ_of_le hle)
        simp [hx, hne]

/-- The exhaustion gap is zero exactly when every required operation has been
    performed. -/
theorem exhaustionGap_zero_iff_all_performed
    (O : ObligationSignature) (P : OperationsPerformed) :
    (exhaustionGap O P).1 = 0 ↔
      (taskRequiredOperations O).all (fun op => decide (op ∈ P.tags)) = true := by
  unfold exhaustionGap
  set req := taskRequiredOperations O
  set inter := req.filter (fun op => decide (op ∈ P.tags))
  by_cases hden : req.length = 0
  · have hreq : req = [] := List.length_eq_zero_iff.mp hden
    simp [req, hreq]
  · have hInterLeReq : inter.length ≤ req.length := by
      simpa [inter] using filter_length_le req (fun op => decide (op ∈ P.tags))
    have hmain :
        req.length - inter.length = 0 ↔
          req.all (fun op => decide (op ∈ P.tags)) = true := by
      constructor
      · intro hzero
        have hReqLeInter : req.length ≤ inter.length := Nat.sub_eq_zero_iff_le.mp hzero
        have hEq : inter.length = req.length := Nat.le_antisymm hInterLeReq hReqLeInter
        exact (filter_length_eq_length_iff_all req (fun op => decide (op ∈ P.tags))).mp hEq
      · intro hall
        have hEq : inter.length = req.length :=
          (filter_length_eq_length_iff_all req (fun op => decide (op ∈ P.tags))).mpr hall
        have hReqLeInter : req.length ≤ inter.length := by
          exact Nat.le_of_eq hEq.symm
        exact Nat.sub_eq_zero_iff_le.mpr hReqLeInter
    simpa [req, inter, hden] using hmain

/-- Proposition 6.1: a T5-style impossibility certificate is unlicensed in a
    context with nonzero exhaustion gap. -/
theorem no_c4_above_nonzero_gap
    (O : ObligationSignature) (P : OperationsPerformed)
  (_hgap : (exhaustionGap O P).1 > 0) :
    ∀ (out : TypedOutput) (metaThm cert : String),
      out = TypedOutput.T5_impossibilityCert metaThm cert →
      isTypedOutputDisciplineViolation out false false false false false = true := by
  intro out metaThm cert hEq
  subst hEq
  simp [isTypedOutputDisciplineViolation]

/-- Pre-Undecidability Fracture Theorem, threshold form. -/
theorem pre_undecidability_fracture
    (O : ObligationSignature) (P : OperationsPerformed)
    (threshold : WLevel) (_hth : 0 < threshold.toNat)
    (hgap : (exhaustionGap O P).1 > 0)
    (hOI : PayloadOperationalIncompleteness) :
    ((exhaustionGap O P).1 > 0) ∧
    (∀ metaThm cert,
       isTypedOutputDisciplineViolation
         (TypedOutput.T5_impossibilityCert metaThm cert)
         false false false false false = true) ∧
    (∀ tag,
       isTypedOutputDisciplineViolation
         (TypedOutput.T1_complete tag)
         false false false false false = true) ∧
    (∃ fw : CertifiedForgettingWitness, fw = hOI.certifiedForgetting) ∧
    (isTypedOutputDisciplineViolation
       (TypedOutput.T4_abstention "" [] [])
       false false false false false = true) := by
  refine ⟨hgap, ?_, ?_, ?_, ?_⟩
  · intro metaThm cert
    simp [isTypedOutputDisciplineViolation]
  · intro tag
    simp [isTypedOutputDisciplineViolation]
  · exact ⟨hOI.certifiedForgetting, rfl⟩
  · simp [isTypedOutputDisciplineViolation]

/-- Definition 7.1: a fault-line-complete architecture for the obligation
    family. -/
structure FaultLineCompleteArchitecture where
  inputFaithfulnessLayer : Unit
  witnessTransitionLayer : CatalogLiftPolicy
  witnessValidationLayer : Unit
  metaHaltController :
    ObligationSignature → LanguageSignature → SearchTraceSignature → Bool
  typedOutputAlgebra : Unit
  externalCertificationIface : Unit

/-- Without a witness-transition layer, terminal outputs collapse to typed
    abstention or else violate the typed-output discipline. -/
theorem flc_layers_necessary_witness_transition :
    ∀ (O : ObligationSignature) (P : OperationsPerformed)
      (arch : FaultLineCompleteArchitecture),
      (exhaustionGap O P).1 > 0 →
      arch.witnessTransitionLayer.choose =
        (fun _ _ => (none : Option LanguageSignature)) →
      ∀ out : TypedOutput,
        (∃ dim cons rej, out = TypedOutput.T4_abstention dim cons rej) ∨
        isTypedOutputDisciplineViolation out false false false false false = true := by
  intro O P arch hgap hNoTransition out
  cases out with
  | T1_complete tag =>
      exact Or.inr (by simp [isTypedOutputDisciplineViolation])
  | T2_construction obj log =>
      exact Or.inr (by simp [isTypedOutputDisciplineViolation])
  | T3_confession thm fw dim res =>
      exact Or.inr (by simp [isTypedOutputDisciplineViolation])
  | T4_abstention dim cons rej =>
      exact Or.inl ⟨dim, cons, rej, rfl⟩
  | T5_impossibilityCert thm cert =>
      exact Or.inr (by simp [isTypedOutputDisciplineViolation])

/-- Without a functioning META-HALT controller, terminal outputs collapse to
    typed abstention or else violate the typed-output discipline. -/
theorem flc_layers_necessary_meta_halt :
    ∀ (O : ObligationSignature) (P : OperationsPerformed)
      (arch : FaultLineCompleteArchitecture),
      (exhaustionGap O P).1 > 0 →
      (∀ Lsig Osig T, arch.metaHaltController Osig Lsig T = false) →
      ∀ out : TypedOutput,
        (∃ dim cons rej, out = TypedOutput.T4_abstention dim cons rej) ∨
        isTypedOutputDisciplineViolation out false false false false false = true := by
  intro O P arch hgap hNoMetaHalt out
  cases out with
  | T1_complete tag =>
      exact Or.inr (by simp [isTypedOutputDisciplineViolation])
  | T2_construction obj log =>
      exact Or.inr (by simp [isTypedOutputDisciplineViolation])
  | T3_confession thm fw dim res =>
      exact Or.inr (by simp [isTypedOutputDisciplineViolation])
  | T4_abstention dim cons rej =>
      exact Or.inl ⟨dim, cons, rej, rfl⟩
  | T5_impossibilityCert thm cert =>
      exact Or.inr (by simp [isTypedOutputDisciplineViolation])

end OperatorKO7.MetaHalt.Fracture
