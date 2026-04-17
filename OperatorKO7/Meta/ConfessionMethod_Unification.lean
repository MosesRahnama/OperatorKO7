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
