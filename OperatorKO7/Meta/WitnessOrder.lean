import OperatorKO7.Kernel
import OperatorKO7.Meta.PolyInterpretation_FullStep
import OperatorKO7.Meta.MPO_FullStep
import OperatorKO7.Meta.DependencyPairs_Works
import OperatorKO7.Meta.DP_BaseOrder_Boundary
import OperatorKO7.Meta.EscapeTrichotomy
import Mathlib.Order.WellFounded

/-!
# Witness-order split for KO7

This module starts the authoritative Phase 1 repair for the cross-paper
witness-order story.

The immediate goal is to separate three layers that the manuscripts must not
collapse into one:

- `directWhole`     : explicit direct whole-term witness families formalized in
  the Paper A barrier stack;
- `importedWhole`   : mathematically sound witnesses over the original KO7
  relation that import structure from outside those direct families;
- `transformedCall` : witnesses that first arise after explicit passage to the
  recursive-call relation.

At this stage the module is intentionally narrow and authoritative:

- the direct layer is represented by the explicit KO7 direct-orienter universe
  already formalized in `EscapeTrichotomy`;
- the imported-whole layer is populated by the existing nonlinear polynomial
  and KO7-specialized MPO proofs;
- the transformed-call layer is populated by the existing dependency-pair
  proof and its linear base-order note.

This is enough to block the specific cross-paper ambiguity now:
Paper C must not present the contract layer as if it were the truth layer.
-/

namespace OperatorKO7.WitnessOrder

open OperatorKO7
open OperatorKO7.Trace

/-- Coarse witness-language levels used by the KO7 cross-paper bridge. -/
inductive WLevel
  | directWhole
  | importedWhole
  | transformedCall
  | externalCert
deriving DecidableEq, Repr

namespace WLevel

def toNat : WLevel → Nat
  | directWhole => 0
  | importedWhole => 1
  | transformedCall => 2
  | externalCert => 3

instance : LE WLevel := ⟨fun a b => a.toNat ≤ b.toNat⟩
instance : LT WLevel := ⟨fun a b => a.toNat < b.toNat⟩

instance (a b : WLevel) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.toNat ≤ b.toNat))
instance (a b : WLevel) : Decidable (a < b) := inferInstanceAs (Decidable (a.toNat < b.toNat))

@[simp] theorem toNat_directWhole : toNat directWhole = 0 := rfl
@[simp] theorem toNat_importedWhole : toNat importedWhole = 1 := rfl
@[simp] theorem toNat_transformedCall : toNat transformedCall = 2 := rfl
@[simp] theorem toNat_externalCert : toNat externalCert = 3 := rfl

end WLevel

/-- A witness tower assigns to each coarse witness level the proposition
    expressing that KO7 has a witness at that level. -/
def WitnessTower := WLevel → Prop

def HasWitness (T : WitnessTower) (ℓ : WLevel) : Prop := T ℓ

def kappaLe (T : WitnessTower) (ℓ : WLevel) : Prop :=
  ∃ j : WLevel, j.toNat ≤ ℓ.toNat ∧ HasWitness T j

def kappaGt (T : WitnessTower) (ℓ : WLevel) : Prop :=
  ∀ j : WLevel, j.toNat ≤ ℓ.toNat → ¬ HasWitness T j

/-- Benchmark contract viewed only at the coarse witness-language level. -/
structure TaskContract where
  admissible : WLevel → Prop

def contractTower (T : WitnessTower) (Γ : TaskContract) : WitnessTower :=
  fun ℓ => Γ.admissible ℓ ∧ T ℓ

/-- The benchmark contract excludes direct whole-term and imported-whole
    witnesses, and permits transformed-call or external-certificate routes. -/
def benchmarkContract : TaskContract where
  admissible
    | .directWhole => False
    | .importedWhole => False
    | .transformedCall => True
    | .externalCert => True

/-- The explicit direct witness universe already formalized in Paper A's KO7
    barrier stack. -/
def DirectWholeWitness : Prop :=
  ∃ O : OperatorKO7.EscapeTrichotomy.KO7DirectOrienter,
    OperatorKO7.EscapeTrichotomy.KO7DirectBarrierRepresentable O ∧ O.Orients

/-- KO7 witness tower used by the cross-paper repair. -/
def ko7Tower : WitnessTower
  | .directWhole => DirectWholeWitness
  | .importedWhole => WellFounded (fun a b : Trace => Step b a)
  | .transformedCall => WellFounded OperatorKO7.MetaDependencyPairs.DPPairRev
  | .externalCert => True

/-- No explicit direct whole-term witness from the formalized KO7 direct
    universe can orient the full KO7 root relation. -/
theorem no_representable_direct_orienter :
    ∀ {O : OperatorKO7.EscapeTrichotomy.KO7DirectOrienter},
      OperatorKO7.EscapeTrichotomy.KO7DirectBarrierRepresentable O → ¬ O.Orients := by
  intro O hrepr
  cases hrepr with
  | additive M =>
      exact fun horient => (OperatorKO7.CompositionalImpossibility.no_global_step_orientation_additive_compositional M) horient
  | compositionalTransparent CM htransparent =>
      exact fun horient =>
        (OperatorKO7.CompositionalImpossibility.no_global_step_orientation_compositional_transparent_delta CM htransparent) horient
  | affineWithPump M =>
      exact fun horient => (PumpedBarrierClasses.no_global_step_orientation_affine_with_pump M) horient
  | quadraticWithPump M =>
      exact fun horient => (PumpedBarrierClasses.no_global_step_orientation_quadratic_with_pump M) horient
  | crossQuadraticWithPump M =>
      exact fun horient => (PumpedBarrierClasses.no_global_step_orientation_cross_quadratic_with_pump M) horient
  | multilinearWithPump M =>
      exact fun horient => (PumpedBarrierClasses.no_global_step_orientation_multilinear_with_pump M) horient
  | polynomialWithPump M =>
      exact fun horient => (PumpedBarrierClasses.no_global_step_orientation_polynomial_with_pump M) horient
  | maxWithPump M =>
      exact fun horient => (PumpedBarrierClasses.no_global_step_orientation_max_with_pump M) horient
  | depth M =>
      exact fun horient => (OperatorKO7.DepthBarrier.no_global_step_orientation_maxDepth M) horient
  | precedence M =>
      exact fun horient => (OperatorKO7.PrecedenceBarrier.no_global_step_orientation_headPrecedenceFamily M) horient
  | matrix2ComponentwiseWithPrimaryPump M =>
      exact fun horient => (PumpedBarrierClasses.no_global_step_orientation_matrix2_with_primary_pump M) horient
  | matrix2LexWithPrimaryPump M =>
      exact fun horient => (PumpedBarrierClasses.no_global_step_orientation_matrix2_lex_with_primary_pump M) horient

/-- There is no witness in the formalized direct whole-term KO7 universe. -/
theorem ko7_no_directWhole_witness :
    ¬ HasWitness ko7Tower WLevel.directWhole := by
  intro h
  rcases h with ⟨O, hrepr, horient⟩
  exact no_representable_direct_orienter hrepr horient

/-- KO7 has a truth-level imported-whole witness via the nonlinear polynomial
    interpretation. -/
theorem ko7_has_importedWhole_witness_poly :
    HasWitness ko7Tower WLevel.importedWhole := by
  exact OperatorKO7.PolyInterpretation.wf_StepRev_poly

/-- KO7 also has a truth-level imported-whole witness via the specialized MPO. -/
theorem ko7_has_importedWhole_witness_mpo :
    HasWitness ko7Tower WLevel.importedWhole := by
  exact OperatorKO7.MetaMPO.wf_StepRev_mpo

/-- KO7 has a transformed-call witness via the dependency-pair relation. -/
theorem ko7_has_transformedCall_witness :
    HasWitness ko7Tower WLevel.transformedCall := by
  exact OperatorKO7.MetaDependencyPairs.wf_DPPairRev

/-- The transformed-call witness still admits a simple linear base order on the
    extracted dependency-pair problem. -/
theorem ko7_transformedCall_has_linear_base_order :
    ∃ μ : Trace → Nat, ∀ {a b : Trace}, OperatorKO7.MetaDependencyPairs.DPPair a b → μ b < μ a := by
  exact OperatorKO7.DPBaseOrderBoundary.extracted_dp_problem_has_linear_base_order

/-- `κ_direct(KO7) > directWhole`: there is no witness at or below the direct
    whole-term layer. -/
theorem ko7_kappaDirect_gt_directWhole :
    kappaGt ko7Tower WLevel.directWhole := by
  intro j hj
  cases j with
  | directWhole =>
      simpa [HasWitness] using ko7_no_directWhole_witness
  | importedWhole =>
      simp [WLevel.toNat] at hj
  | transformedCall =>
      simp [WLevel.toNat] at hj
  | externalCert =>
      simp [WLevel.toNat] at hj

/-- `κ_truth(KO7) ≤ importedWhole`: a mathematically sound witness exists at
    the imported-whole layer. -/
theorem ko7_kappaTruth_le_importedWhole :
    kappaLe ko7Tower WLevel.importedWhole := by
  exact ⟨WLevel.importedWhole, by decide, ko7_has_importedWhole_witness_poly⟩

/-- The benchmark contract excludes imported-whole witnesses even when they are
    mathematically sound. -/
theorem benchmarkContract_disallows_importedWhole :
    ¬ benchmarkContract.admissible WLevel.importedWhole := by
  simp [benchmarkContract]

/-- No benchmark-contract witness exists at or below the imported-whole level. -/
theorem ko7_kappaContract_gt_importedWhole :
    kappaGt (contractTower ko7Tower benchmarkContract) WLevel.importedWhole := by
  intro j hj
  cases j with
  | directWhole =>
      simp [HasWitness, contractTower, benchmarkContract, ko7Tower]
  | importedWhole =>
      simp [HasWitness, contractTower, benchmarkContract, ko7Tower]
  | transformedCall =>
      simp [WLevel.toNat] at hj
  | externalCert =>
      simp [WLevel.toNat] at hj

/-- `κ_contract(KO7, Γ_bench) ≤ transformedCall`: the benchmark contract first
    becomes satisfiable at the transformed-call layer. -/
theorem ko7_kappaContract_le_transformedCall :
    kappaLe (contractTower ko7Tower benchmarkContract) WLevel.transformedCall := by
  refine ⟨WLevel.transformedCall, by decide, ?_⟩
  exact ⟨by simp [benchmarkContract], ko7_has_transformedCall_witness⟩

/-- Paper-facing summary of the three-layer split currently justified inside the
    authoritative KO7 theorem stack. -/
theorem ko7_three_kappa_summary :
    kappaGt ko7Tower WLevel.directWhole
      ∧ kappaLe ko7Tower WLevel.importedWhole
      ∧ kappaGt (contractTower ko7Tower benchmarkContract) WLevel.importedWhole
      ∧ kappaLe (contractTower ko7Tower benchmarkContract) WLevel.transformedCall := by
  exact ⟨ko7_kappaDirect_gt_directWhole,
    ko7_kappaTruth_le_importedWhole,
    ko7_kappaContract_gt_importedWhole,
    ko7_kappaContract_le_transformedCall⟩

/-- Paper-facing corollary: under the benchmark contract, the first admissible
    KO7 witness sits at the transformed-call layer rather than at the truth
    layer where imported-whole witnesses already exist. -/
theorem ko7_kappaContract_has_transformedCall :
    kappaGt (contractTower ko7Tower benchmarkContract) WLevel.importedWhole
      ∧ kappaLe (contractTower ko7Tower benchmarkContract) WLevel.transformedCall := by
  exact ⟨ko7_kappaContract_gt_importedWhole, ko7_kappaContract_le_transformedCall⟩

end OperatorKO7.WitnessOrder
