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
    (hgap : (exhaustionGap O P).1 > 0) :
    ¬ (taskRequiredOperations O).all (fun op => decide (op ∈ P.tags)) = true ∧
    ∀ (out : TypedOutput) (metaThm cert : String),
      out = TypedOutput.T5_impossibilityCert metaThm cert →
      isTypedOutputDisciplineViolation out false false false false false = true := by
  refine ⟨?_, ?_⟩
  · intro hall
    have hzero : (exhaustionGap O P).1 = 0 :=
      (exhaustionGap_zero_iff_all_performed O P).2 hall
    exact Nat.ne_of_gt hgap hzero
  · intro out metaThm cert hEq
    subst hEq
    simp [isTypedOutputDisciplineViolation]

/-- Pre-Undecidability Fracture Theorem, threshold form. -/
theorem pre_undecidability_fracture
    (C : Catalog) (policy : CatalogLiftPolicy)
    (admiss : AdmissibilityTable) (loops : LoopPatternTable)
    (inner : InnerSearchStep)
    (O : ObligationSignature) (P : OperationsPerformed)
    (s : SupervisoryLoopState)
    (threshold : WLevel) (hth : 0 < threshold.toNat)
    (hgap : (exhaustionGap O P).1 > 0)
    (hOI : PayloadOperationalIncompleteness)
    (hconf : ∀ L ∈ s.visited, L.level.toNat < threshold.toNat)
    (hsound : ∀ (L : LanguageSignature) (o : TypedOutput),
      supervisoryLoop (C.size + 1) C policy admiss loops inner O s [] =
        .acceptedWitness L o →
      isTypedOutputDisciplineViolation o false false false false false = false) :
    kappaGt (contractTower ko7Tower benchmarkContract) WLevel.importedWhole ∧
    ((exhaustionGap O P).1 > 0) ∧
    (¬ (taskRequiredOperations O).all (fun op => decide (op ∈ P.tags)) = true) ∧
    (∀ metaThm cert,
       isTypedOutputDisciplineViolation
         (TypedOutput.T5_impossibilityCert metaThm cert)
         false false false false false = true) ∧
    ((∃ rec : AuditCompleteC3Record,
        supervisoryLoop (C.size + 1) C policy admiss loops inner O s [] = .auditC3 rec) ∨
     (∃ L o,
        supervisoryLoop (C.size + 1) C policy admiss loops inner O s [] = .acceptedWitness L o ∧
        L.level.toNat ≥ threshold.toNat)) ∧
    (∃ fw : CertifiedForgettingWitness, fw = hOI.certifiedForgetting) ∧
    (isTypedOutputDisciplineViolation
       (TypedOutput.T4_abstention "" [] [])
       false false false false false = true) := by
  have hc4 := no_c4_above_nonzero_gap O P hgap
  have hmeta :=
    below_threshold_forces_metahalt
      C policy admiss loops inner O s threshold hth hconf hsound
  refine ⟨hOI.noContractWitnessBelowImportedWhole, hgap, hc4.1, ?_, hmeta, ?_, ?_⟩
  · intro metaThm cert
    exact hc4.2 (TypedOutput.T5_impossibilityCert metaThm cert) metaThm cert rfl
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
    ∀ (C : Catalog) (admiss : AdmissibilityTable) (loops : LoopPatternTable)
      (inner : InnerSearchStep) (O : ObligationSignature)
      (P : OperationsPerformed) (s : SupervisoryLoopState)
      (arch : FaultLineCompleteArchitecture),
      (exhaustionGap O P).1 > 0 →
      arch.witnessTransitionLayer.choose =
        (fun _ _ => (none : Option LanguageSignature)) →
      let out :=
        supervisoryLoop (C.size + 1) C arch.witnessTransitionLayer admiss loops inner O s []
      (¬ (taskRequiredOperations O).all (fun op => decide (op ∈ P.tags)) = true) ∧
      (∃ rec : AuditCompleteC3Record, out = .auditC3 rec) := by
  intro C admiss loops inner O P s arch hgap hNoTransition
  dsimp
  have hc4 := no_c4_above_nonzero_gap O P hgap
  have hterm :=
    supervisoryLoop_emits_c3_or_c1c2 C arch.witnessTransitionLayer admiss loops inner O s
  refine ⟨hc4.1, ?_⟩
  rcases hterm with hacc | haudit
  · rcases hacc with ⟨L, o, hacc⟩
    simp [supervisoryLoop, hNoTransition] at hacc
  · exact haudit

/-- Without a functioning META-HALT controller, terminal outputs collapse to
    typed abstention or else violate the typed-output discipline. -/
theorem flc_layers_necessary_meta_halt :
    ∀ (C : Catalog) (admiss : AdmissibilityTable) (loops : LoopPatternTable)
      (inner : InnerSearchStep) (O : ObligationSignature)
      (P : OperationsPerformed) (s : SupervisoryLoopState)
      (threshold : WLevel) (arch : FaultLineCompleteArchitecture),
      0 < threshold.toNat →
      (exhaustionGap O P).1 > 0 →
      (∀ Lsig Osig T, arch.metaHaltController Osig Lsig T = false) →
      (∀ (Osig : ObligationSignature) (Lsig : LanguageSignature)
          (T : SearchTraceSignature) (budget catalogRem : Nat),
          arch.metaHaltController Osig Lsig T = false →
          metaHalt Osig Lsig T admiss loops budget catalogRem = none) →
      (∀ L ∈ s.visited, L.level.toNat < threshold.toNat) →
      (∀ (L : LanguageSignature) (o : TypedOutput),
        supervisoryLoop (C.size + 1) C arch.witnessTransitionLayer admiss loops inner O s [] =
          .acceptedWitness L o →
        isTypedOutputDisciplineViolation o false false false false false = false) →
      let out :=
        supervisoryLoop (C.size + 1) C arch.witnessTransitionLayer admiss loops inner O s []
      (¬ (taskRequiredOperations O).all (fun op => decide (op ∈ P.tags)) = true) ∧
      (∀ (Lsig : LanguageSignature) (T : SearchTraceSignature) (budget catalogRem : Nat),
        metaHalt O Lsig T admiss loops budget catalogRem = none) ∧
      ((∃ rec : AuditCompleteC3Record, out = .auditC3 rec) ∨
       (∃ L o, out = .acceptedWitness L o ∧ L.level.toNat ≥ threshold.toNat)) := by
  intro C admiss loops inner O P s threshold arch hth hgap hNoMetaHalt hReflectsNone hconf hsound
  dsimp
  have hc4 := no_c4_above_nonzero_gap O P hgap
  have hallNone :
      ∀ (Lsig : LanguageSignature) (T : SearchTraceSignature) (budget catalogRem : Nat),
        metaHalt O Lsig T admiss loops budget catalogRem = none := by
    intro Lsig T budget catalogRem
    exact hReflectsNone O Lsig T budget catalogRem (hNoMetaHalt Lsig O T)
  have hterm :=
    below_threshold_forces_metahalt
      C arch.witnessTransitionLayer admiss loops inner O s threshold hth hconf hsound
  exact ⟨hc4.1, hallNone, hterm⟩

end OperatorKO7.MetaHalt.Fracture
