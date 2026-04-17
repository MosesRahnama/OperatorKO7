import OperatorKO7.Meta.WitnessOrder
import OperatorKO7.Meta.CompositionalMeasure_Impossibility
import OperatorKO7.Meta.ConfessionMethod

/-!
# Operational incompleteness for the duplicated payload coordinate

This module packages a narrow theorem-backed notion of **operational
incompleteness** for the KO7 duplicating recursor.

The claim formalized here is intentionally precise:

- the direct whole-term witness language for KO7 is empty;
- mathematically sound witnesses do exist above that layer;
- under the benchmark contract the first admissible witness appears only at the
  transformed-call layer;
- the transformed witness is carried by a rank that explicitly drops wrapper
  sensitivity, i.e. it works only by **certified forgetting** of the duplicated
  payload coordinate.

This is a witness-language incompleteness statement, not an undecidability
statement. The point is not that the duplicated payload is meaningless, but
that the direct whole-term proof language cannot remain fully sensitive to it
and still certify the KO7 duplicating step.
-/

namespace OperatorKO7.MetaOperationalIncompleteness

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.WitnessOrder
open OperatorKO7.ConfessionMethodFamily

/-- A transformed witness that succeeds by orienting the duplicating step while
explicitly violating wrapper sensitivity on the duplicated payload coordinate.

This is the narrow formal content behind the informal phrase "ignore the
payload": the witness comes with an explicit rank, and that rank can be shown
not to satisfy the wrapper-subterm sensitivity expected of the direct
whole-term barrier families. -/
structure CertifiedForgettingWitness where
  rank : Trace → Nat
  orientsDupStep :
    ∀ b s n, rank (app s (recΔ b s n)) < rank (recΔ b s (delta n))
  violatesPayloadLeft :
    ∃ x y : Trace, ¬ (rank (app x y) > rank x)
  violatesPayloadRight :
    ∃ x y : Trace, ¬ (rank (app x y) > rank y)

/-- KO7's dependency-pair projection is the canonical certified-forgetting
witness in the current artifact. -/
def dpCertifiedForgettingWitness : CertifiedForgettingWitness where
  rank := OperatorKO7.CompositionalImpossibility.dpProjection
  orientsDupStep := OperatorKO7.CompositionalImpossibility.dp_projection_orients_rec_succ
  violatesPayloadLeft := OperatorKO7.CompositionalImpossibility.dp_projection_violates_sensitivity
  violatesPayloadRight := OperatorKO7.CompositionalImpossibility.dp_projection_violates_subterm2

/-- Explicit equivalence between the schema carrier of `ko7Schema` and the
    concrete kernel syntax `Trace`. Making this map explicit avoids relying on
    reducibility heuristics in downstream packaging lemmas. -/
def ko7CarrierEquivTrace : OperatorKO7.CompositionalImpossibility.ko7Schema.T ≃ Trace := by
  dsimp [OperatorKO7.CompositionalImpossibility.ko7Schema]
  exact Equiv.refl _

/-- Any KO7 confession method yields a certified-forgetting witness: the
underlying projection rank already orients the duplicating step and violates
wrapper sensitivity on both payload coordinates. -/
def CertifiedForgettingWitness.ofConfessionMethod
    (C : ConfessionMethod OperatorKO7.CompositionalImpossibility.ko7Schema) :
    CertifiedForgettingWitness where
  rank := fun t => C.rank (ko7CarrierEquivTrace.symm t)
  orientsDupStep := by
    intro b s n
    simpa [ko7CarrierEquivTrace, OperatorKO7.CompositionalImpossibility.ko7Schema] using
      confession_orients C
        (ko7CarrierEquivTrace.symm b)
        (ko7CarrierEquivTrace.symm s)
        (ko7CarrierEquivTrace.symm n)
  violatesPayloadLeft := by
    rcases confession_violates_wrap1 C with ⟨x, y, hxy⟩
    refine ⟨ko7CarrierEquivTrace x, ko7CarrierEquivTrace y, ?_⟩
    simpa [ko7CarrierEquivTrace, OperatorKO7.CompositionalImpossibility.ko7Schema] using hxy
  violatesPayloadRight := by
    rcases confession_violates_wrap2 C with ⟨x, y, hxy⟩
    refine ⟨ko7CarrierEquivTrace x, ko7CarrierEquivTrace y, ?_⟩
    simpa [ko7CarrierEquivTrace, OperatorKO7.CompositionalImpossibility.ko7Schema] using hxy

@[simp] theorem CertifiedForgettingWitness.ofConfessionMethod_rank
    (C : ConfessionMethod OperatorKO7.CompositionalImpossibility.ko7Schema) :
    (CertifiedForgettingWitness.ofConfessionMethod C).rank =
      fun t => C.rank (ko7CarrierEquivTrace.symm t) := rfl

/-- Narrow formal package for operational incompleteness at the duplicated
payload coordinate.

Interpretation:
- there is no witness in the direct whole-term KO7 witness universe;
- truth-level witnesses exist above that universe;
- under the benchmark contract the first admissible witness sits at the
  transformed-call layer;
- that transformed-call witness succeeds by certified forgetting of wrapper
  sensitivity on the duplicated payload coordinate. -/
structure PayloadOperationalIncompleteness where
  noDirectWhole :
    ¬ HasWitness ko7Tower WLevel.directWhole
  truthWitnessImported :
    HasWitness ko7Tower WLevel.importedWhole
  noContractWitnessBelowImportedWhole :
    kappaGt (contractTower ko7Tower benchmarkContract) WLevel.importedWhole
  contractWitnessAtTransformedCall :
    kappaLe (contractTower ko7Tower benchmarkContract) WLevel.transformedCall
  certifiedForgetting :
    CertifiedForgettingWitness

/-- KO7 exhibits payload-level operational incompleteness in the sense above. -/
def ko7PayloadOperationalIncompleteness : PayloadOperationalIncompleteness where
  noDirectWhole := ko7_no_directWhole_witness
  truthWitnessImported := ko7_has_importedWhole_witness_poly
  noContractWitnessBelowImportedWhole := ko7_kappaContract_gt_importedWhole
  contractWitnessAtTransformedCall := ko7_kappaContract_le_transformedCall
  certifiedForgetting := dpCertifiedForgettingWitness

/-- Paper-facing packaged constant for the same formal object. -/
def ko7_operationally_incomplete_at_payload :
    PayloadOperationalIncompleteness :=
  ko7PayloadOperationalIncompleteness

/-- A sharper corollary: any benchmark-admissible KO7 witness must live above
the imported-whole layer, and the artifact already exhibits one whose rank
works only by violating wrapper sensitivity. -/
theorem ko7_admissible_witness_requires_certified_forgetting :
    kappaGt (contractTower ko7Tower benchmarkContract) WLevel.importedWhole
      ∧ kappaLe (contractTower ko7Tower benchmarkContract) WLevel.transformedCall
      ∧ (∃ _ : CertifiedForgettingWitness, True) := by
  refine ⟨ko7_kappaContract_gt_importedWhole, ko7_kappaContract_le_transformedCall, ?_⟩
  exact ⟨dpCertifiedForgettingWitness, trivial⟩

/-- The dependency-pair projection witness is explicit evidence that the
successful transformed-call layer is not wrapper-sensitive on the duplicated
payload coordinate. -/
theorem dp_projection_exhibits_certified_forgetting :
    ∃ fw : CertifiedForgettingWitness, fw.rank = OperatorKO7.CompositionalImpossibility.dpProjection := by
  exact ⟨dpCertifiedForgettingWitness, rfl⟩

end OperatorKO7.MetaOperationalIncompleteness
