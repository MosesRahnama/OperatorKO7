import OperatorKO7.Meta.ConfessionMethod
import OperatorKO7.Meta.CompositionalMeasure_Impossibility
import OperatorKO7.Meta.DependencyPairs_Works

/-!
# Confession Method Instance: Dependency Pairs + Subterm Criterion

The canonical confession method on the KO7 step-duplicating schema.

Dependency pairs extract the recursive-call relation from the rules,
construct the dependency-pair graph, and apply the subterm criterion with
projection π(recΔ♯) = 3 to certify that the counter coordinate strictly
decreases. The wrapper `app(s, ·)` and the duplicated payload `s` are
dropped from the proof obligation. Soundness is licensed by the
Arts–Giesl 2000 theorem.

The underlying `ProjectionRank` is `dpProjectionRank` from
`CompositionalMeasure_Impossibility.lean`, already fully formalized.
This module packages it as a `ConfessionMethod` instance.
-/

namespace OperatorKO7.ConfessionMethodFamily

open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.MetaDependencyPairs

/-- A route-local dependency-pair witness on the marked recursive symbol.
    On KO7, the marked pair still carries the three original recursor
    coordinates, and the third coordinate is the unique descent-bearing one. -/
structure DPWitness where
  selectedCoordinate : Fin 3
  selectedCoordinate_is_counter : selectedCoordinate = ⟨2, by decide⟩

/-- The concrete dependency-pair witness on the KO7 schema. -/
def schemaDPWitness : DPWitness where
  selectedCoordinate := ⟨2, by decide⟩
  selectedCoordinate_is_counter := rfl

/-- The DP witness packaged as the intermediate confession-core witness. -/
def DPWitness.toConfessionCoreWitness (_W : DPWitness) : ConfessionCoreWitness ko7Schema where
  rank := dpProjection
  rank_base := by rfl
  rank_succ := by intro t; rfl
  rank_wrap := by intro x y; rfl
  rank_recur := by intro b s n; rfl

/-- Explicit marked-pair view for the DP route on the single recursive call. -/
structure DPPairShapeEvidence where
  caller : Trace
  callee : Trace
  callerShape : ∃ b s n, caller = recΔ b s (delta n)
  calleeShape : ∃ b s n, callee = recΔ b s n

/-- Stronger pair-problem semantics for the DP route: the marked pair comes
    directly from the KO7 `rec_succ` rule instance, is an extracted dependency
    pair, strictly decreases the DP rank, and lives in a well-founded reverse
    pair problem. -/
structure DPPairProblemEvidence where
  caller : Trace
  rhs : Trace
  callee : Trace
  extractedFromStep : Step caller rhs
  dependencyPair : DPPair caller callee
  strictRankDescent : MetaDependencyPairs.dpRank callee < MetaDependencyPairs.dpRank caller

/-- The concrete pair-problem semantics for the schema's single recursive
    dependency pair. -/
def schemaDPPairProblemEvidence (b s n : Trace) : DPPairProblemEvidence where
  caller := recΔ b s (delta n)
  rhs := app s (recΔ b s n)
  callee := recΔ b s n
  extractedFromStep := (rec_succ_extracts_dependency_pair b s n).1
  dependencyPair := (rec_succ_extracts_dependency_pair b s n).2
  strictRankDescent := by
    exact dpPair_decreases (rec_succ_extracts_dependency_pair b s n).2

/-- The concrete marked-pair view for the schema's single recursive call. -/
def schemaDPPairShapeEvidence (b s n : Trace) : DPPairShapeEvidence where
  caller := recΔ b s (delta n)
  callee := recΔ b s n
  callerShape := ⟨b, s, n, rfl⟩
  calleeShape := ⟨b, s, n, rfl⟩

/-- Dependency pairs + subterm criterion as a confession method on KO7. -/
def dpConfession : ConfessionMethod ko7Schema where
  toProjectionRank := dpProjectionRank
  license := SoundnessLicense.artsGiesl2000

/-- The DP confession is the canonical confession-core route on KO7. -/
theorem dpConfession_is_canonical :
    dpConfession.toProjectionRank = dpProjectionRank := rfl

/-- The DP witness selects the counter coordinate as the descent-bearing
    argument on the marked recursive pair. -/
theorem dpWitness_selects_counter_coordinate :
    schemaDPWitness.selectedCoordinate = ⟨2, by decide⟩ :=
  schemaDPWitness.selectedCoordinate_is_counter

/-- The DP route realizes the canonical confession core directly. -/
theorem dpWitness_realizes_projection_core :
    dpConfession.rank = dpProjectionRank.rank := rfl

/-- The DP witness induces the canonical intermediate confession core. -/
theorem dpWitness_toConfessionCoreWitness_eq_core :
    schemaDPWitness.toConfessionCoreWitness.toProjectionRank = dpProjectionRank := by
  rfl

/-- Richer route-local evidence for the DP entry route. This packages the
    selected coordinate together with concrete local facts about the marked
    recursive-pair shape that are stronger than mere final rank equality. -/
structure DPRouteEvidence where
  witness : DPWitness
  markedPairShape : Trace → Trace → Trace → DPPairShapeEvidence
  pairProblemSemantics : Trace → Trace → Trace → DPPairProblemEvidence
  stepShape :
    ∀ (b s n : Trace),
      witness.toConfessionCoreWitness.rank (recΔ b s (delta n)) =
        witness.toConfessionCoreWitness.rank n + 1
  wrapperPayloadDropped :
    ∀ (x y : Trace), witness.toConfessionCoreWitness.rank (app x y) = 0
  pairProblemWellFounded : WellFounded MetaDependencyPairs.DPPairRev

/-- The concrete rich DP route evidence on KO7. -/
def schemaDPRouteEvidence : DPRouteEvidence where
  witness := schemaDPWitness
  markedPairShape := schemaDPPairShapeEvidence
  pairProblemSemantics := schemaDPPairProblemEvidence
  stepShape := by
    intro b s n
    rfl
  wrapperPayloadDropped := by
    intro x y
    rfl
  pairProblemWellFounded := wf_DPPairRev

/-- The richer DP route evidence already entails the generic semantic profile. -/
theorem dpRouteEvidence_implies_semantic_profile :
    NormalizedAtBase ko7Schema schemaDPRouteEvidence.witness.toConfessionCoreWitness.rank
    ∧ TracksSuccessorDepth ko7Schema schemaDPRouteEvidence.witness.toConfessionCoreWitness.rank
    ∧ ForgetsWrapperPayload ko7Schema schemaDPRouteEvidence.witness.toConfessionCoreWitness.rank
    ∧ FollowsRecursiveCounter ko7Schema schemaDPRouteEvidence.witness.toConfessionCoreWitness.rank := by
  exact schemaDPRouteEvidence.witness.toConfessionCoreWitness.satisfies_semantic_profile

/-- The DP witness directly satisfies the generic semantic confession profile. -/
theorem dpWitness_has_semantic_profile :
    NormalizedAtBase ko7Schema schemaDPWitness.toConfessionCoreWitness.rank
    ∧ TracksSuccessorDepth ko7Schema schemaDPWitness.toConfessionCoreWitness.rank
    ∧ ForgetsWrapperPayload ko7Schema schemaDPWitness.toConfessionCoreWitness.rank
    ∧ FollowsRecursiveCounter ko7Schema schemaDPWitness.toConfessionCoreWitness.rank := by
  exact schemaDPWitness.toConfessionCoreWitness.satisfies_semantic_profile

end OperatorKO7.ConfessionMethodFamily
