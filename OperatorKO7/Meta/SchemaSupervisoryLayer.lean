import OperatorKO7.Meta.SchemaWitnessOrder

/-!
# Schema-Level Supervisory Discipline and PRT Boundary Copies

Schema-level abstract copies of the Section 6 supervisory layer from Paper 2.

This module does **not** reimplement the concrete KO7 META-HALT loop. Instead it
packages the structural supervisory facts at the reusable schema level:

- typed supervisory outputs and regimes;
- valid supervisory META-HALT events;
- the impossibility of satisfying supervisory correctness by issuing an
  internal untyped terminal verdict below the witness boundary;
- an abstract boundary-object package;
- false-formal-legitimacy detection as a failure of the four PRT clauses.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

open SchemaWitnessTower

/-- Schema-level typed supervisory outputs, mirroring the five Paper 2 output
classes but without committing to the KO7-specific supervisory loop. -/
inductive SupervisoryOutput
  | terminalVerdict (label : String)
  | construction (constructionObject : String) (verifierLog : String)
  | confession
      (externalTheorem : String)
      (externalFramework : String)
      (droppedDimension : String)
      (residualDerivationTag : String)
  | typedAbstention
      (operationallyIncompleteDimension : String)
      (frameworksConsidered : List String)
      (frameworksRejected : List String)
  | impossibilityCert
      (metaTheoremReference : String)
      (checkableCertificateTag : String)
  deriving DecidableEq, Repr

/-- Terminal vs non-terminal supervisory regimes. -/
inductive SupervisoryRegime
  | terminal
  | nonterminal
  deriving DecidableEq, Repr

/-- A supervisory state is just a regime/output pair at the schema level. -/
structure SupervisoryRecord where
  regime : SupervisoryRegime
  output : SupervisoryOutput

/-- Well-formed T3 confession. -/
def WellFormedConfession : SupervisoryOutput → Prop
  | .confession thm fw dim res =>
      thm ≠ "" ∧ fw ≠ "" ∧ dim ≠ "" ∧ res ≠ ""
  | _ => False

/-- Well-formed T4 typed abstention. -/
def WellFormedTypedAbstention : SupervisoryOutput → Prop
  | .typedAbstention dim cons rej =>
      dim ≠ "" ∧ cons ≠ [] ∧ rej ≠ []
  | _ => False

/-- Internal object-level "undecidable" / "impossible" style stop from within
an inadequate witness basis. This is intentionally broader than the literal
string values: any terminal verdict-shaped stop counts. -/
def InternalMetaHaltClaim : SupervisoryOutput → Prop
  | .terminalVerdict _ => True
  | .impossibilityCert thm cert => thm = "" ∨ cert = ""
  | _ => False

/-- Definition 6.5 / valid supervisory META-HALT: a non-terminal supervisory
state whose emitted record is either a well-formed T3 confession or a
well-formed T4 abstention. -/
def ValidSupervisoryMetaHalt (r : SupervisoryRecord) : Prop :=
  r.regime = SupervisoryRegime.nonterminal
    ∧ (WellFormedConfession r.output ∨ WellFormedTypedAbstention r.output)

/-- A witness-language shift succeeds exactly when a well-formed confession is
emitted and the transformed-call witness layer is actually available. -/
def WitnessShiftAt {S : StepDuplicatingSchema}
    (T : SchemaWitnessTower S) (x : S.T) (out : SupervisoryOutput) : Prop :=
  WellFormedConfession out ∧ HasWitness T x WLevel.transformedCall

/-- Schema-level supervisory correctness for an obligation at a witness
boundary: once direct-whole evidence is blocked, the only internally honest
responses are either a witness-language shift (T3 confession) or a well-formed
T4 typed abstention. -/
def SupervisoryCorrectAt {S : StepDuplicatingSchema}
    (T : SchemaWitnessTower S) (x : S.T) (r : SupervisoryRecord) : Prop :=
  OB T x →
    r.regime = SupervisoryRegime.nonterminal
      ∧ (WitnessShiftAt T x r.output ∨ WellFormedTypedAbstention r.output)

/-- Corollary 6.4: an internal untyped object-level undecidability/impossibility
stop is not a valid supervisory META-HALT certificate. -/
theorem object_undecidability_not_valid_supervisory_verdict
    (r : SupervisoryRecord)
    (hinternal : InternalMetaHaltClaim r.output) :
    ¬ ValidSupervisoryMetaHalt r := by
  intro hvalid
  cases r with
  | mk regime output =>
      cases output <;>
        simp [ValidSupervisoryMetaHalt, WellFormedConfession,
          WellFormedTypedAbstention, InternalMetaHaltClaim] at hvalid hinternal ⊢

/-- Any witness shift is already a valid supervisory META-HALT event. -/
theorem witnessShiftAt_valid_supervisory_metaHalt
    {S : StepDuplicatingSchema}
    (T : SchemaWitnessTower S) (x : S.T)
    (r : SupervisoryRecord)
    (hreg : r.regime = SupervisoryRegime.nonterminal)
    (hshift : WitnessShiftAt T x r.output) :
    ValidSupervisoryMetaHalt r := by
  refine ⟨hreg, Or.inl hshift.1⟩

/-- Any well-formed typed abstention is a valid supervisory META-HALT event. -/
theorem typedAbstention_valid_supervisory_metaHalt
    (r : SupervisoryRecord)
    (hreg : r.regime = SupervisoryRegime.nonterminal)
    (habs : WellFormedTypedAbstention r.output) :
    ValidSupervisoryMetaHalt r := by
  exact ⟨hreg, Or.inr habs⟩

/-- Proposition 6.8: if the current witness basis is itself under adequacy
challenge, supervisory correctness cannot be satisfied by an internal untyped
terminal stop. -/
theorem supervisory_no_internal_metahalt
    {S : StepDuplicatingSchema}
    (T : SchemaWitnessTower S) (x : S.T)
    (r : SupervisoryRecord)
    (hboundary : OB T x)
    (hinternal : InternalMetaHaltClaim r.output) :
    ¬ SupervisoryCorrectAt T x r := by
  intro hcorrect
  have hcorrect' := hcorrect hboundary
  rcases hcorrect' with ⟨hreg, hgood | habs⟩
  · exact object_undecidability_not_valid_supervisory_verdict r hinternal
      (witnessShiftAt_valid_supervisory_metaHalt T x r hreg hgood)
  · exact object_undecidability_not_valid_supervisory_verdict r hinternal
      (typedAbstention_valid_supervisory_metaHalt r hreg habs)

/-- Abstract schema-level PRT boundary object. This is the reusable version of
Paper 2 Proposition 6.9: an obligation is a genuine boundary object when the
first adequate witness lies above the direct-whole layer and the surrounding
benchmarking context is not an arbitrary hard case but a structurally minimal,
externally settled, substrate-close one. -/
structure PRTBoundaryObject {S : StepDuplicatingSchema}
    (T : SchemaWitnessTower S) (x : S.T) where
  closeToSubstrate : Prop
  closeToSubstrate_holds : closeToSubstrate
  structurallyMinimal : Prop
  structurallyMinimal_holds : structurallyMinimal
  externallySettled : Prop
  externallySettled_holds : externallySettled
  orientationBoundary : OB T x
  transformedCallWitness : HasWitness T x WLevel.transformedCall

/-- A PRT boundary object has a nontrivial witness-language shift by
construction. -/
theorem boundary_object_has_nontrivial_shift
    {S : StepDuplicatingSchema}
    {T : SchemaWitnessTower S} {x : S.T}
    (B : PRTBoundaryObject T x) :
    OB T x ∧ kappaLe T x WLevel.transformedCall := by
  refine ⟨B.orientationBoundary, ?_⟩
  exact ⟨WLevel.transformedCall, Nat.le_refl _, B.transformedCallWitness⟩

/-- Proposition 6.9 in operational form: for a genuine boundary object, an
internal terminal stop is rejected by the supervisory clause. -/
theorem prt_boundary_object_rejects_internal_terminal_verdict
    {S : StepDuplicatingSchema}
    {T : SchemaWitnessTower S} {x : S.T}
    (B : PRTBoundaryObject T x)
    (r : SupervisoryRecord)
    (hinternal : InternalMetaHaltClaim r.output) :
    ¬ SupervisoryCorrectAt T x r := by
  exact supervisory_no_internal_metahalt T x r B.orientationBoundary hinternal

/-- Schema-level PRT evaluation profile. -/
structure PRTEvaluation {S : StepDuplicatingSchema}
    (T : SchemaWitnessTower S) (x : S.T) where
  output : SupervisoryOutput
  truthCorrect : Prop
  witnessCorrect : Prop
  boundaryCorrect : Prop
  supervisoryCorrect : Prop

/-- Output has the surface form of formal reasoning. -/
def SurfaceFormalOutput : SupervisoryOutput → Prop
  | .terminalVerdict label => label ≠ ""
  | .construction obj log => obj ≠ "" ∧ log ≠ ""
  | .confession thm fw dim res =>
      thm ≠ "" ∧ fw ≠ "" ∧ dim ≠ "" ∧ res ≠ ""
  | .typedAbstention dim cons rej => dim ≠ "" ∧ cons ≠ [] ∧ rej ≠ []
  | .impossibilityCert thm cert => thm ≠ "" ∧ cert ≠ ""

/-- Definition 6.10 / false formal legitimacy. -/
def FalseFormalLegitimacy {S : StepDuplicatingSchema}
    {T : SchemaWitnessTower S} {x : S.T}
    (E : PRTEvaluation T x) : Prop :=
  ¬ E.truthCorrect
    ∨ ¬ E.witnessCorrect
    ∨ ¬ E.boundaryCorrect
    ∨ ¬ E.supervisoryCorrect

/-- Proposition 6.11: once a proof-shaped output fails any one of the four PRT
clauses, the system has exhibited false formal legitimacy on that obligation. -/
theorem prt_failure_detects_false_formal_legitimacy
    {S : StepDuplicatingSchema}
    {T : SchemaWitnessTower S} {x : S.T}
    (E : PRTEvaluation T x)
    (_hsurface : SurfaceFormalOutput E.output)
    (hfail : ¬ E.truthCorrect
      ∨ ¬ E.witnessCorrect
      ∨ ¬ E.boundaryCorrect
      ∨ ¬ E.supervisoryCorrect) :
    FalseFormalLegitimacy E :=
  hfail

/-- Systematic PRT failure across a family. -/
def SystematicPRTFailure {S : StepDuplicatingSchema}
    (T : SchemaWitnessTower S)
    (Eval : ∀ x : S.T, PRTEvaluation T x) : Prop :=
  ∃ x, FalseFormalLegitimacy (Eval x)

/-- Repeated proof-interface failure across a schema family yields false formal
legitimacy somewhere in that family. -/
theorem systematic_failure_yields_false_formal_legitimacy
    {S : StepDuplicatingSchema}
    (T : SchemaWitnessTower S)
    (Eval : ∀ x : S.T, PRTEvaluation T x)
    (x : S.T)
    (_hsurface : SurfaceFormalOutput (Eval x).output)
    (hfail : ¬ (Eval x).truthCorrect
      ∨ ¬ (Eval x).witnessCorrect
      ∨ ¬ (Eval x).boundaryCorrect
      ∨ ¬ (Eval x).supervisoryCorrect) :
    SystematicPRTFailure T Eval := by
  exact ⟨x, prt_failure_detects_false_formal_legitimacy (Eval x) _hsurface hfail⟩

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
