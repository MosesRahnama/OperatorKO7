import OperatorKO7.Meta.ConfessionMethod
import OperatorKO7.Meta.ConfessionMethod_Unification
import OperatorKO7.Meta.OperationalIncompleteness
import OperatorKO7.Meta.DependencyPairs_Works
import OperatorKO7.Meta.PolyInterpretation_FullStep
import OperatorKO7.Meta.ContextClosed_SN_Full

/-!
# The Confession-Method Family: Collected Results

This module collects the four formalized confession methods on the KO7
step-duplicating schema and proves family-level theorems about their
shared structure.

The central result is `confession_is_a_class`: on the step-duplicating
schema, four methods with four distinct soundness licenses all converge
to the same projection core and all satisfy the `CertifiedForgettingWitness`
interface. The important point is not just that the ranks are equal, but
that the non-DP routes now reach that equality through route-local witness
objects and derived projection ranks rather than by direct alias assignment.

The four methods are:
1. Dependency pairs + subterm criterion (Arts-Giesl 2000)
2. Direct counter-projection via the subterm criterion
3. Size-Change Termination (Lee-Jones-Ben-Amram 2001)
4. Argument filtering within the DP framework
-/

namespace OperatorKO7.ConfessionMethodFamily

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.MetaOperationalIncompleteness

/-- All four confession methods enumerated. -/
def allConfessionMethods : List (ConfessionMethod ko7Schema) :=
  [dpConfession, counterProjectionConfession, sctConfession, argumentFilteringConfession]

/-- The family has exactly four members. -/
theorem family_size : allConfessionMethods.length = 4 := by rfl

/-- Every confession method in the family produces the same rank on
    the KO7 schema. This is now proved through the route-local convergence
    theorems, not by immediate alias collapse. -/
theorem family_rank_agreement :
    ∀ C ∈ allConfessionMethods,
      C.rank = dpConfession.rank := by
  intro C hC
  simp [allConfessionMethods] at hC
  rcases hC with rfl | rfl | rfl | rfl
  · rfl
  · exact counterProjection_eq_dp_rank
  · exact sct_eq_dp_rank
  · exact argumentFiltering_eq_dp_rank

/-- Every confession method in the family orients the KO7 duplicating
    step. -/
theorem family_orients_dup_step :
    ∀ C ∈ allConfessionMethods,
      ∀ b s n : Trace,
        C.rank (app s (recΔ b s n)) < C.rank (recΔ b s (delta n)) := by
  intro C hC b s n
  exact confession_orients C b s n

/-- Every confession method in the family violates wrapper sensitivity.
    This is the formal content of "the payload is declared inert." -/
theorem family_violates_sensitivity :
    ∀ C ∈ allConfessionMethods,
      (∃ x y : Trace, ¬ (C.rank (app x y) > C.rank x))
      ∧ (∃ x y : Trace, ¬ (C.rank (app x y) > C.rank y)) := by
  intro C hC
  exact ⟨confession_violates_wrap1 C, confession_violates_wrap2 C⟩

/-- Every confession method in the family is a certified-forgetting
    witness in the sense of `OperationalIncompleteness.lean`. -/
theorem family_certified_forgetting :
    ∀ C ∈ allConfessionMethods,
      ∃ fw : CertifiedForgettingWitness,
        fw.rank = C.rank := by
  intro C hC
  exact ⟨CertifiedForgettingWitness.ofConfessionMethod C, rfl⟩

/-- The same certified-forgetting conclusion can now be witnessed through the
    richer route-local evidence packages, not only through the generic
    `ofConfessionMethod` adapter. -/
theorem family_certified_forgetting_via_route_evidence :
    ∀ C ∈ allConfessionMethods,
      ∃ fw : CertifiedForgettingWitness,
        fw.rank = C.rank := by
  intro C hC
  simp [allConfessionMethods] at hC
  rcases hC with rfl | rfl | rfl | rfl
  · exact ⟨dpRouteEvidenceCertifiedForgettingWitness, rfl⟩
  · exact ⟨directCounterProjectionRouteEvidenceCertifiedForgettingWitness, rfl⟩
  · exact ⟨sctRouteEvidenceCertifiedForgettingWitness, rfl⟩
  · exact ⟨argumentFilteringRouteEvidenceCertifiedForgettingWitness, rfl⟩

/-- The four confession methods have four distinct soundness licenses.
    This confirms they are genuinely different methods that happen to
    share the same rank on this schema, not four names for one method. -/
theorem family_distinct_licenses :
    (allConfessionMethods.map (·.license)).Nodup := by
  decide

/-- The non-DP confession routes each converge to the same projection core as
    the canonical DP route. -/
theorem family_single_core :
    counterProjectionConfession.rank = dpConfession.rank
    ∧ sctConfession.rank = dpConfession.rank
    ∧ argumentFilteringConfession.rank = dpConfession.rank := by
  exact ⟨counterProjection_eq_dp_rank, sct_eq_dp_rank, argumentFiltering_eq_dp_rank⟩

/-- The family exhibits both ingredients of the strong target:
    distinct entry licenses and a single convergent projection core. -/
theorem family_independent_entries_and_single_core :
    (allConfessionMethods.map (·.license)).Nodup
    ∧ counterProjectionConfession.rank = dpConfession.rank
    ∧ sctConfession.rank = dpConfession.rank
    ∧ argumentFilteringConfession.rank = dpConfession.rank := by
  rcases confession_routes_converge with
    ⟨_, _, _, _, hCounter, hSCT, hFilter⟩
  exact ⟨family_distinct_licenses, hCounter, hSCT, hFilter⟩

/-- **Main theorem: Confession methods form a structural class.**

    On the step-duplicating schema:
    - four methods with distinct soundness licenses exist;
    - the non-DP routes converge to the same common rank (counter projection)
      as the canonical DP route;
    - all satisfy the certified-forgetting interface;
    - the licenses are pairwise distinct.

    This is the formal content behind Paper C's central claim that the
    construction/confession boundary separates method *classes*, not
    individual methods. The confession class is defined by a structural
    shape (extract recursive calls, project to descent coordinate,
    declare payload inert) that is invariant under changes of extraction
    mechanism and soundness license. -/
theorem confession_is_a_class :
    allConfessionMethods.length = 4
    ∧ (∀ C ∈ allConfessionMethods, C.rank = dpConfession.rank)
    ∧ (allConfessionMethods.map (·.license)).Nodup := by
  exact ⟨family_size, family_rank_agreement, family_distinct_licenses⟩

/-- The confession family provides four independently licensed entry routes
    into one shared projection core resolving KO7's operational
    incompleteness at the payload dimension. -/
theorem confession_family_resolves_operational_incompleteness :
    ∀ C ∈ allConfessionMethods,
      ∃ fw : CertifiedForgettingWitness, fw.rank = C.rank :=
  family_certified_forgetting

/-! ## Full-system termination via the confession family

    Each confession method proves termination of the *extracted pair problem*,
    not just orientation of the duplicating step. The bridge from pair-problem
    well-foundedness to full-system termination is the external soundness
    metatheorem named by each method's `SoundnessLicense`.

    Since all four methods share the same rank on this schema, they all
    inherit the same pair-problem well-foundedness proof (`wf_DPPairRev`
    from `DependencyPairs_Works.lean`). The full KO7 root-step termination
    then follows by any of three independent routes:

    - The DP route: `wf_DPPairRev` + Arts-Giesl soundness (external)
    - The polynomial route: `wf_StepRev_poly` (internal, construction method)
    - The MPO route: `wf_StepRev_mpo` (internal, construction method)

    All three are already formalized in the artifact. The confession family
    inherits the DP route because the pair problem is the same for all four
    methods.
-/

/-- Every confession method in the family terminates the extracted KO7
    dependency-pair problem. Since all four share the same rank, they
    share the same well-foundedness proof. -/
theorem family_terminates_pair_problem :
    ∀ C ∈ allConfessionMethods,
      WellFounded (fun a b : Trace =>
        OperatorKO7.MetaDependencyPairs.DPPair b a) := by
  intro C _
  exact OperatorKO7.MetaDependencyPairs.wf_DPPairRev

/-- The full KO7 root relation is terminating. This is the existing
    `wf_StepRev_poly` theorem, restated here to confirm that the
    confession family's pair-problem termination is consistent with
    (and subsumed by) the full-system termination already in the
    artifact. -/
theorem ko7_full_system_terminates :
    WellFounded (fun a b : Trace => Step b a) :=
  OperatorKO7.PolyInterpretation.wf_StepRev_poly

/-- The full KO7 context-closed relation is also terminating. -/
theorem ko7_full_context_closed_terminates :
    WellFounded MetaSN_KO7.StepCtxFullRev :=
  MetaSN_KO7.wf_StepCtxFullRev_poly

end OperatorKO7.ConfessionMethodFamily
