import OperatorKO7.Meta.ConfessionMethod_DP
import OperatorKO7.Meta.ConfessionMethod_CounterProjection
import OperatorKO7.Meta.ConfessionMethod_SCT
import OperatorKO7.Meta.ConfessionMethod_ArgumentFiltering
import OperatorKO7.Meta.SchemaForgettingWitness
import OperatorKO7.Meta.OperationalIncompleteness

/-!
# Confession Method Unification

This module isolates the convergence layer for the four confession-method
entry routes formalized on KO7.

Each route now has its own local witness object and derived projection rank:

- dependency pairs,
- direct counter projection,
- size-change termination,
- argument filtering.

The theorems here record the second half of the strong target: although the
routes are independently licensed and enter through different local witness
objects, they all converge to one shared confession core on KO7.
-/

namespace OperatorKO7.ConfessionMethodFamily

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.CompositionalImpossibility

/-- The common confession core on KO7 is the canonical DP projection rank. -/
abbrev confessionProjectionCore : ProjectionRank ko7Schema := dpProjectionRank

/-- The common method-agnostic confession-core witness on KO7. -/
abbrev confessionCoreWitness : ConfessionCoreWitness ko7Schema :=
  ConfessionCoreWitness.ofProjectionRank confessionProjectionCore

/-- The four concrete routes viewed as confession-core witnesses. -/
abbrev dpCoreWitness := dpConfession.toConfessionCoreWitness
abbrev counterProjectionCoreWitness := counterProjectionConfession.toConfessionCoreWitness
abbrev sctCoreWitness := sctConfession.toConfessionCoreWitness
abbrev argumentFilteringCoreWitness := argumentFilteringConfession.toConfessionCoreWitness

/-- KO7-local side conditions for the non-schema constructors. These are not
    part of the primitive step-duplicating schema, but they are needed for a
    genuine uniqueness theorem on the full `Trace` carrier. -/
def CollapsesIntegrate (rank : Trace → Nat) : Prop :=
  ∀ t, rank (Trace.integrate t) = 0

def CollapsesMerge (rank : Trace → Nat) : Prop :=
  ∀ x y, rank (Trace.merge x y) = 0

def CollapsesEqW (rank : Trace → Nat) : Prop :=
  ∀ x y, rank (Trace.eqW x y) = 0

/-- The common confession core satisfies the generic semantic profile. -/
theorem confession_core_has_semantic_profile :
    NormalizedAtBase ko7Schema confessionCoreWitness.rank
    ∧ TracksSuccessorDepth ko7Schema confessionCoreWitness.rank
    ∧ ForgetsWrapperPayload ko7Schema confessionCoreWitness.rank
    ∧ FollowsRecursiveCounter ko7Schema confessionCoreWitness.rank := by
  exact confessionCoreWitness.satisfies_semantic_profile

/-- The common confession core also collapses KO7's non-schema constructors. -/
theorem confession_core_has_ko7_extended_semantic_profile :
    NormalizedAtBase ko7Schema confessionCoreWitness.rank
    ∧ TracksSuccessorDepth ko7Schema confessionCoreWitness.rank
    ∧ ForgetsWrapperPayload ko7Schema confessionCoreWitness.rank
    ∧ FollowsRecursiveCounter ko7Schema confessionCoreWitness.rank
    ∧ CollapsesIntegrate confessionCoreWitness.rank
    ∧ CollapsesMerge confessionCoreWitness.rank
    ∧ CollapsesEqW confessionCoreWitness.rank := by
  refine ⟨confession_core_has_semantic_profile.1,
    confession_core_has_semantic_profile.2.1,
    confession_core_has_semantic_profile.2.2.1,
    confession_core_has_semantic_profile.2.2.2,
    ?_, ?_, ?_⟩
  · intro t
    rfl
  · intro x y
    rfl
  · intro x y
    rfl

/-- KO7-local uniqueness: any rank on the full `Trace` carrier that matches
    the confession-core semantic behavior on the schema constructors and also
    collapses the non-schema constructors must coincide with the canonical DP
    projection rank. -/
theorem ko7_extended_semantic_profile_unique
    {rank : Trace → Nat}
    (hbase : NormalizedAtBase ko7Schema rank)
    (hsucc : TracksSuccessorDepth ko7Schema rank)
    (hwrap : ForgetsWrapperPayload ko7Schema rank)
    (hrecur : FollowsRecursiveCounter ko7Schema rank)
    (hintegrate : CollapsesIntegrate rank)
    (hmerge : CollapsesMerge rank)
    (heqW : CollapsesEqW rank) :
    rank = dpProjection := by
  funext t
  induction t with
  | void =>
      simpa [NormalizedAtBase, dpProjection] using hbase
  | delta t ih =>
      simpa [TracksSuccessorDepth, dpProjection, ih] using hsucc t
  | integrate t ih =>
      simpa [CollapsesIntegrate, dpProjection] using hintegrate t
  | merge x y ihx ihy =>
      simpa [CollapsesMerge, dpProjection] using hmerge x y
  | app x y ihx ihy =>
      simpa [ForgetsWrapperPayload, dpProjection] using hwrap x y
  | recΔ b s n ihb ihs ihn =>
      simpa [FollowsRecursiveCounter, dpProjection, ihn] using hrecur b s n
  | eqW x y ihx ihy =>
      simpa [CollapsesEqW, dpProjection] using heqW x y

/-- The route-local witness objects also induce the same confession core. -/
theorem all_route_local_witnesses_share_confession_core :
    schemaDPWitness.toConfessionCoreWitness.toProjectionRank = confessionProjectionCore
    ∧ schemaDirectCounterProjectionWitness.toConfessionCoreWitness.toProjectionRank =
        confessionProjectionCore
    ∧ schemaSCTWitness.toConfessionCoreWitness.toProjectionRank = confessionProjectionCore
    ∧ schemaArgumentFilteringWitness.toConfessionCoreWitness.toProjectionRank =
        confessionProjectionCore := by
  exact ⟨dpWitness_toConfessionCoreWitness_eq_core,
    directCounterProjectionWitness_toConfessionCoreWitness_eq_core,
    sctWitness_toConfessionCoreWitness_eq_core,
    argumentFilteringWitness_toConfessionCoreWitness_eq_core⟩

/-- The route-local witness objects are equal to the common intermediate
    confession-core witness, not only after projection-rank packaging. -/
theorem all_route_local_witnesses_share_confession_core_witness_exact :
    schemaDPWitness.toConfessionCoreWitness = confessionCoreWitness
    ∧ schemaDirectCounterProjectionWitness.toConfessionCoreWitness = confessionCoreWitness
    ∧ schemaSCTWitness.toConfessionCoreWitness = confessionCoreWitness
    ∧ schemaArgumentFilteringWitness.toConfessionCoreWitness = confessionCoreWitness := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rfl
  · apply ConfessionCoreWitness.ext_rank
    intro t
    simpa [confessionCoreWitness, ConfessionCoreWitness.ofProjectionRank,
      DirectCounterProjectionWitness.toConfessionCoreWitness] using
      congrFun counterProjectionRankFn_eq_dpProjection t
  · apply ConfessionCoreWitness.ext_rank
    intro t
    simpa [confessionCoreWitness, ConfessionCoreWitness.ofProjectionRank,
      SCTWitness.toConfessionCoreWitness] using
      congrFun sctRankFn_eq_dpProjection t
  · apply ConfessionCoreWitness.ext_rank
    intro t
    simpa [confessionCoreWitness, ConfessionCoreWitness.ofProjectionRank,
      ArgumentFilteringWitness.toConfessionCoreWitness] using
      congrFun argumentFilteringRankFn_eq_dpProjection t

/-- The DP route is the canonical realization of the confession core. -/
theorem dp_route_eq_confession_core :
    dpConfession.toProjectionRank = confessionProjectionCore := rfl

/-- Direct counter projection converges to the same confession core. -/
theorem counterProjection_route_eq_confession_core :
    counterProjectionConfession.toProjectionRank = confessionProjectionCore := by
  rw [counterProjectionConfession_is_derived]
  exact counterProjectionDerivedRank_eq_dpProjectionRank

/-- SCT converges to the same confession core. -/
theorem sct_route_eq_confession_core :
    sctConfession.toProjectionRank = confessionProjectionCore := by
  rw [sctConfession_is_derived]
  exact sctDerivedRank_eq_dpProjectionRank

/-- Argument filtering converges to the same confession core. -/
theorem argumentFiltering_route_eq_confession_core :
    argumentFilteringConfession.toProjectionRank = confessionProjectionCore := by
  rw [argumentFilteringConfession_is_derived]
  exact argumentFilteringDerivedRank_eq_dpProjectionRank

/-- All four confession routes coincide at the level of projection ranks. -/
theorem all_confession_routes_share_projection_core :
    dpConfession.toProjectionRank = confessionProjectionCore
    ∧ counterProjectionConfession.toProjectionRank = confessionProjectionCore
    ∧ sctConfession.toProjectionRank = confessionProjectionCore
    ∧ argumentFilteringConfession.toProjectionRank = confessionProjectionCore := by
  exact ⟨dp_route_eq_confession_core, counterProjection_route_eq_confession_core,
    sct_route_eq_confession_core, argumentFiltering_route_eq_confession_core⟩

/-- The same convergence can be stated at the level of the intermediate
    confession-core witness. -/
theorem all_confession_routes_share_confession_core_witness :
    dpCoreWitness.toProjectionRank = confessionProjectionCore
    ∧ counterProjectionCoreWitness.toProjectionRank = confessionProjectionCore
    ∧ sctCoreWitness.toProjectionRank = confessionProjectionCore
    ∧ argumentFilteringCoreWitness.toProjectionRank = confessionProjectionCore := by
  exact ⟨dp_route_eq_confession_core, counterProjection_route_eq_confession_core,
    sct_route_eq_confession_core, argumentFiltering_route_eq_confession_core⟩

/-- The concrete confession methods also agree with the common intermediate
    confession-core witness exactly, not only after reprojecting to
    `ProjectionRank`. -/
theorem all_confession_methods_share_confession_core_witness_exact :
    dpCoreWitness = confessionCoreWitness
    ∧ counterProjectionCoreWitness = confessionCoreWitness
    ∧ sctCoreWitness = confessionCoreWitness
    ∧ argumentFilteringCoreWitness = confessionCoreWitness := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rfl
  · apply ConfessionCoreWitness.ext_rank
    intro t
    simpa [counterProjectionCoreWitness, confessionCoreWitness,
      ConfessionMethod.toConfessionCoreWitness, ConfessionCoreWitness.ofProjectionRank] using
      congrFun counterProjectionRankFn_eq_dpProjection t
  · apply ConfessionCoreWitness.ext_rank
    intro t
    simpa [sctCoreWitness, confessionCoreWitness,
      ConfessionMethod.toConfessionCoreWitness, ConfessionCoreWitness.ofProjectionRank] using
      congrFun sctRankFn_eq_dpProjection t
  · apply ConfessionCoreWitness.ext_rank
    intro t
    simpa [argumentFilteringCoreWitness, confessionCoreWitness,
      ConfessionMethod.toConfessionCoreWitness, ConfessionCoreWitness.ofProjectionRank] using
      congrFun argumentFilteringRankFn_eq_dpProjection t

/-- Consequently, all four concrete confession methods satisfy the same generic
    semantic profile once viewed through the intermediate core witness. -/
theorem all_confession_methods_share_semantic_profile :
    (NormalizedAtBase ko7Schema dpCoreWitness.rank
      ∧ TracksSuccessorDepth ko7Schema dpCoreWitness.rank
      ∧ ForgetsWrapperPayload ko7Schema dpCoreWitness.rank
      ∧ FollowsRecursiveCounter ko7Schema dpCoreWitness.rank)
    ∧ (NormalizedAtBase ko7Schema counterProjectionCoreWitness.rank
      ∧ TracksSuccessorDepth ko7Schema counterProjectionCoreWitness.rank
      ∧ ForgetsWrapperPayload ko7Schema counterProjectionCoreWitness.rank
      ∧ FollowsRecursiveCounter ko7Schema counterProjectionCoreWitness.rank)
    ∧ (NormalizedAtBase ko7Schema sctCoreWitness.rank
      ∧ TracksSuccessorDepth ko7Schema sctCoreWitness.rank
      ∧ ForgetsWrapperPayload ko7Schema sctCoreWitness.rank
      ∧ FollowsRecursiveCounter ko7Schema sctCoreWitness.rank)
    ∧ (NormalizedAtBase ko7Schema argumentFilteringCoreWitness.rank
      ∧ TracksSuccessorDepth ko7Schema argumentFilteringCoreWitness.rank
      ∧ ForgetsWrapperPayload ko7Schema argumentFilteringCoreWitness.rank
      ∧ FollowsRecursiveCounter ko7Schema argumentFilteringCoreWitness.rank) := by
  rcases all_confession_methods_share_confession_core_witness_exact with
    ⟨hDP, hCounter, hSCT, hFilter⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [hDP] using confession_core_has_semantic_profile
  · simpa [hCounter] using confession_core_has_semantic_profile
  · simpa [hSCT] using confession_core_has_semantic_profile
  · simpa [hFilter] using confession_core_has_semantic_profile

/-- The route-local witness objects also satisfy the generic semantic profile
    directly, without first passing through equality to the common core. -/
theorem all_route_local_witnesses_have_semantic_profile_directly :
    (NormalizedAtBase ko7Schema schemaDPWitness.toConfessionCoreWitness.rank
      ∧ TracksSuccessorDepth ko7Schema schemaDPWitness.toConfessionCoreWitness.rank
      ∧ ForgetsWrapperPayload ko7Schema schemaDPWitness.toConfessionCoreWitness.rank
      ∧ FollowsRecursiveCounter ko7Schema schemaDPWitness.toConfessionCoreWitness.rank)
    ∧ (NormalizedAtBase ko7Schema schemaDirectCounterProjectionWitness.toConfessionCoreWitness.rank
      ∧ TracksSuccessorDepth ko7Schema schemaDirectCounterProjectionWitness.toConfessionCoreWitness.rank
      ∧ ForgetsWrapperPayload ko7Schema schemaDirectCounterProjectionWitness.toConfessionCoreWitness.rank
      ∧ FollowsRecursiveCounter ko7Schema schemaDirectCounterProjectionWitness.toConfessionCoreWitness.rank)
    ∧ (NormalizedAtBase ko7Schema schemaSCTWitness.toConfessionCoreWitness.rank
      ∧ TracksSuccessorDepth ko7Schema schemaSCTWitness.toConfessionCoreWitness.rank
      ∧ ForgetsWrapperPayload ko7Schema schemaSCTWitness.toConfessionCoreWitness.rank
      ∧ FollowsRecursiveCounter ko7Schema schemaSCTWitness.toConfessionCoreWitness.rank)
    ∧ (NormalizedAtBase ko7Schema schemaArgumentFilteringWitness.toConfessionCoreWitness.rank
      ∧ TracksSuccessorDepth ko7Schema schemaArgumentFilteringWitness.toConfessionCoreWitness.rank
      ∧ ForgetsWrapperPayload ko7Schema schemaArgumentFilteringWitness.toConfessionCoreWitness.rank
      ∧ FollowsRecursiveCounter ko7Schema schemaArgumentFilteringWitness.toConfessionCoreWitness.rank) := by
  exact ⟨dpWitness_has_semantic_profile,
    directCounterProjectionWitness_has_semantic_profile,
    sctWitness_has_semantic_profile,
    argumentFilteringWitness_has_semantic_profile⟩

/-- The route-local witness objects also satisfy the KO7-local side conditions
    on the non-schema constructors. -/
theorem all_route_local_witnesses_have_ko7_extended_semantic_profile :
    (NormalizedAtBase ko7Schema schemaDPWitness.toConfessionCoreWitness.rank
      ∧ TracksSuccessorDepth ko7Schema schemaDPWitness.toConfessionCoreWitness.rank
      ∧ ForgetsWrapperPayload ko7Schema schemaDPWitness.toConfessionCoreWitness.rank
      ∧ FollowsRecursiveCounter ko7Schema schemaDPWitness.toConfessionCoreWitness.rank
      ∧ CollapsesIntegrate schemaDPWitness.toConfessionCoreWitness.rank
      ∧ CollapsesMerge schemaDPWitness.toConfessionCoreWitness.rank
      ∧ CollapsesEqW schemaDPWitness.toConfessionCoreWitness.rank)
    ∧ (NormalizedAtBase ko7Schema schemaDirectCounterProjectionWitness.toConfessionCoreWitness.rank
      ∧ TracksSuccessorDepth ko7Schema schemaDirectCounterProjectionWitness.toConfessionCoreWitness.rank
      ∧ ForgetsWrapperPayload ko7Schema schemaDirectCounterProjectionWitness.toConfessionCoreWitness.rank
      ∧ FollowsRecursiveCounter ko7Schema schemaDirectCounterProjectionWitness.toConfessionCoreWitness.rank
      ∧ CollapsesIntegrate schemaDirectCounterProjectionWitness.toConfessionCoreWitness.rank
      ∧ CollapsesMerge schemaDirectCounterProjectionWitness.toConfessionCoreWitness.rank
      ∧ CollapsesEqW schemaDirectCounterProjectionWitness.toConfessionCoreWitness.rank)
    ∧ (NormalizedAtBase ko7Schema schemaSCTWitness.toConfessionCoreWitness.rank
      ∧ TracksSuccessorDepth ko7Schema schemaSCTWitness.toConfessionCoreWitness.rank
      ∧ ForgetsWrapperPayload ko7Schema schemaSCTWitness.toConfessionCoreWitness.rank
      ∧ FollowsRecursiveCounter ko7Schema schemaSCTWitness.toConfessionCoreWitness.rank
      ∧ CollapsesIntegrate schemaSCTWitness.toConfessionCoreWitness.rank
      ∧ CollapsesMerge schemaSCTWitness.toConfessionCoreWitness.rank
      ∧ CollapsesEqW schemaSCTWitness.toConfessionCoreWitness.rank)
    ∧ (NormalizedAtBase ko7Schema schemaArgumentFilteringWitness.toConfessionCoreWitness.rank
      ∧ TracksSuccessorDepth ko7Schema schemaArgumentFilteringWitness.toConfessionCoreWitness.rank
      ∧ ForgetsWrapperPayload ko7Schema schemaArgumentFilteringWitness.toConfessionCoreWitness.rank
      ∧ FollowsRecursiveCounter ko7Schema schemaArgumentFilteringWitness.toConfessionCoreWitness.rank
      ∧ CollapsesIntegrate schemaArgumentFilteringWitness.toConfessionCoreWitness.rank
      ∧ CollapsesMerge schemaArgumentFilteringWitness.toConfessionCoreWitness.rank
      ∧ CollapsesEqW schemaArgumentFilteringWitness.toConfessionCoreWitness.rank) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨dpWitness_has_semantic_profile.1, dpWitness_has_semantic_profile.2.1,
      dpWitness_has_semantic_profile.2.2.1, dpWitness_has_semantic_profile.2.2.2,
      ?_, ?_, ?_⟩
    · intro t; rfl
    · intro x y; rfl
    · intro x y; rfl
  · refine ⟨directCounterProjectionWitness_has_semantic_profile.1,
      directCounterProjectionWitness_has_semantic_profile.2.1,
      directCounterProjectionWitness_has_semantic_profile.2.2.1,
      directCounterProjectionWitness_has_semantic_profile.2.2.2,
      ?_, ?_, ?_⟩
    · intro t; rfl
    · intro x y; rfl
    · intro x y; rfl
  · refine ⟨sctWitness_has_semantic_profile.1,
      sctWitness_has_semantic_profile.2.1,
      sctWitness_has_semantic_profile.2.2.1,
      sctWitness_has_semantic_profile.2.2.2,
      ?_, ?_, ?_⟩
    · intro t; rfl
    · intro x y; rfl
    · intro x y; rfl
  · refine ⟨argumentFilteringWitness_has_semantic_profile.1,
      argumentFilteringWitness_has_semantic_profile.2.1,
      argumentFilteringWitness_has_semantic_profile.2.2.1,
      argumentFilteringWitness_has_semantic_profile.2.2.2,
      ?_, ?_, ?_⟩
    · intro t; rfl
    · intro x y; rfl
    · intro x y; rfl

/-- KO7-local convergence can now be recovered from route-local semantic
    premises plus the extended-profile uniqueness theorem, not only from the
    previously hard-coded rank equalities. -/
theorem all_route_local_witnesses_converge_by_extended_semantic_profile :
    schemaDPWitness.toConfessionCoreWitness.rank = dpProjection
    ∧ schemaDirectCounterProjectionWitness.toConfessionCoreWitness.rank = dpProjection
    ∧ schemaSCTWitness.toConfessionCoreWitness.rank = dpProjection
    ∧ schemaArgumentFilteringWitness.toConfessionCoreWitness.rank = dpProjection := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ko7_extended_semantic_profile_unique
      dpWitness_has_semantic_profile.1
      dpWitness_has_semantic_profile.2.1
      dpWitness_has_semantic_profile.2.2.1
      dpWitness_has_semantic_profile.2.2.2
      (by intro t; rfl)
      (by intro x y; rfl)
      (by intro x y; rfl)
  · exact ko7_extended_semantic_profile_unique
      directCounterProjectionWitness_has_semantic_profile.1
      directCounterProjectionWitness_has_semantic_profile.2.1
      directCounterProjectionWitness_has_semantic_profile.2.2.1
      directCounterProjectionWitness_has_semantic_profile.2.2.2
      (by intro t; rfl)
      (by intro x y; rfl)
      (by intro x y; rfl)
  · exact ko7_extended_semantic_profile_unique
      sctWitness_has_semantic_profile.1
      sctWitness_has_semantic_profile.2.1
      sctWitness_has_semantic_profile.2.2.1
      sctWitness_has_semantic_profile.2.2.2
      (by intro t; rfl)
      (by intro x y; rfl)
      (by intro x y; rfl)
  · exact ko7_extended_semantic_profile_unique
      argumentFilteringWitness_has_semantic_profile.1
      argumentFilteringWitness_has_semantic_profile.2.1
      argumentFilteringWitness_has_semantic_profile.2.2.1
      argumentFilteringWitness_has_semantic_profile.2.2.2
      (by intro t; rfl)
      (by intro x y; rfl)
      (by intro x y; rfl)

/-- Route-local semantic-profile forgetting witnesses, obtained directly from
    the witness-local evidence rather than from projection-core equality. -/
abbrev dpSemanticForgettingWitness : ForgettingWitness ko7Schema :=
  ForgettingWitness.ofSemanticProfile
    schemaDPWitness.toConfessionCoreWitness.rank
    dpWitness_has_semantic_profile.1
    dpWitness_has_semantic_profile.2.1
    dpWitness_has_semantic_profile.2.2.1
    dpWitness_has_semantic_profile.2.2.2

abbrev counterProjectionSemanticForgettingWitness : ForgettingWitness ko7Schema :=
  ForgettingWitness.ofSemanticProfile
    schemaDirectCounterProjectionWitness.toConfessionCoreWitness.rank
    directCounterProjectionWitness_has_semantic_profile.1
    directCounterProjectionWitness_has_semantic_profile.2.1
    directCounterProjectionWitness_has_semantic_profile.2.2.1
    directCounterProjectionWitness_has_semantic_profile.2.2.2

abbrev sctSemanticForgettingWitness : ForgettingWitness ko7Schema :=
  ForgettingWitness.ofSemanticProfile
    schemaSCTWitness.toConfessionCoreWitness.rank
    sctWitness_has_semantic_profile.1
    sctWitness_has_semantic_profile.2.1
    sctWitness_has_semantic_profile.2.2.1
    sctWitness_has_semantic_profile.2.2.2

abbrev argumentFilteringSemanticForgettingWitness : ForgettingWitness ko7Schema :=
  ForgettingWitness.ofSemanticProfile
    schemaArgumentFilteringWitness.toConfessionCoreWitness.rank
    argumentFilteringWitness_has_semantic_profile.1
    argumentFilteringWitness_has_semantic_profile.2.1
    argumentFilteringWitness_has_semantic_profile.2.2.1
    argumentFilteringWitness_has_semantic_profile.2.2.2

/-- The route-local semantic-profile forgetting witnesses recover the same rank
    functions as the corresponding concrete confession methods. -/
theorem all_route_local_witnesses_yield_semantic_forgetting_witnesses :
    dpSemanticForgettingWitness.rank = dpConfession.rank
    ∧ counterProjectionSemanticForgettingWitness.rank = counterProjectionConfession.rank
    ∧ sctSemanticForgettingWitness.rank = sctConfession.rank
    ∧ argumentFilteringSemanticForgettingWitness.rank = argumentFilteringConfession.rank := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The common semantic profile also yields the generic forgetting-witness
    layer directly, without first appealing to equality with the canonical
    projection core. -/
theorem confession_core_semantic_profile_yields_forgetting_witness_rank :
    (ForgettingWitness.ofSemanticProfile confessionCoreWitness.rank
      confession_core_has_semantic_profile.1
      confession_core_has_semantic_profile.2.1
      confession_core_has_semantic_profile.2.2.1
      confession_core_has_semantic_profile.2.2.2).rank
      = dpConfession.toForgettingWitness.rank := by
  rfl

/-- The corresponding rank functions also coincide. -/
theorem all_confession_routes_share_rank_core :
    dpConfession.rank = confessionProjectionCore.rank
    ∧ counterProjectionConfession.rank = confessionProjectionCore.rank
    ∧ sctConfession.rank = confessionProjectionCore.rank
    ∧ argumentFilteringConfession.rank = confessionProjectionCore.rank := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rfl
  · simpa [confessionProjectionCore] using counterProjection_eq_dp_rank
  · simpa [confessionProjectionCore] using sct_eq_dp_rank
  · simpa [confessionProjectionCore] using argumentFiltering_eq_dp_rank

/-- The four concrete routes viewed through the schema-level forgetting-witness
    interface. -/
abbrev dpForgettingWitness := dpConfession.toForgettingWitness
abbrev counterProjectionForgettingWitness := counterProjectionConfession.toForgettingWitness
abbrev sctForgettingWitness := sctConfession.toForgettingWitness
abbrev argumentFilteringForgettingWitness := argumentFilteringConfession.toForgettingWitness

/-- Every confession route yields the generic forgetting-witness structure. -/
theorem all_confession_routes_yield_forgetting_witnesses :
    dpForgettingWitness.rank = dpConfession.rank
    ∧ counterProjectionForgettingWitness.rank = counterProjectionConfession.rank
    ∧ sctForgettingWitness.rank = sctConfession.rank
    ∧ argumentFilteringForgettingWitness.rank = argumentFilteringConfession.rank := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The forgetting-witness layer also factors through the intermediate
    confession-core witness. -/
theorem all_confession_routes_factor_through_confession_core_witness :
    ForgettingWitness.ofConfessionCoreWitness dpCoreWitness = dpForgettingWitness
    ∧ ForgettingWitness.ofConfessionCoreWitness counterProjectionCoreWitness =
        counterProjectionForgettingWitness
    ∧ ForgettingWitness.ofConfessionCoreWitness sctCoreWitness = sctForgettingWitness
    ∧ ForgettingWitness.ofConfessionCoreWitness argumentFilteringCoreWitness =
        argumentFilteringForgettingWitness := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Every confession route also yields a KO7-certified forgetting witness
    without reusing the canonical DP package by equality. -/
theorem all_confession_routes_yield_certified_forgetting_witnesses :
    (OperatorKO7.MetaOperationalIncompleteness.CertifiedForgettingWitness.ofConfessionMethod
      dpConfession).rank = (fun t => dpConfession.rank t)
    ∧ (OperatorKO7.MetaOperationalIncompleteness.CertifiedForgettingWitness.ofConfessionMethod
        counterProjectionConfession).rank =
        counterProjectionConfession.rank
    ∧ (OperatorKO7.MetaOperationalIncompleteness.CertifiedForgettingWitness.ofConfessionMethod
        sctConfession).rank = sctConfession.rank
    ∧ (OperatorKO7.MetaOperationalIncompleteness.CertifiedForgettingWitness.ofConfessionMethod
        argumentFilteringConfession).rank =
        argumentFilteringConfession.rank := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Strong convergence summary: independent route-local witnesses feed one
    shared confession core on KO7. -/
theorem confession_routes_converge :
    schemaDPWitness.selectedCoordinate = ⟨2, by decide⟩
    ∧ schemaDirectCounterProjectionWitness.selectedCoordinate = ⟨2, by decide⟩
    ∧ (∀ i : Fin 3,
        schemaSCTWitness.graph.arcs i i = SCArc.strictDecrease →
        i = ⟨2, by omega⟩)
    ∧ schemaArgumentFilteringWitness.keepRecurCoordinate = ⟨2, by decide⟩
    ∧ counterProjectionConfession.rank = dpConfession.rank
    ∧ sctConfession.rank = dpConfession.rank
    ∧ argumentFilteringConfession.rank = dpConfession.rank := by
  exact ⟨dpWitness_selects_counter_coordinate,
    schemaDirectCounterProjectionWitness.selectedCoordinate_is_counter,
    sctWitness_selects_counter_coordinate,
    schemaArgumentFilteringWitness.keepRecurCoordinate_is_counter,
    counterProjection_eq_dp_rank,
    sct_eq_dp_rank,
    argumentFiltering_eq_dp_rank⟩

end OperatorKO7.ConfessionMethodFamily
