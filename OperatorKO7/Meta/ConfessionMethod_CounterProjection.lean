import OperatorKO7.Meta.ConfessionMethod
import OperatorKO7.Meta.ConfessionMethod_DP

/-!
# Confession Method Instance: Direct Counter-Projection (Subterm Criterion)

The subterm criterion applied directly to argument positions of the defined
symbol F, without passing through the dependency-pair extraction step.

On the two-rule schema:
- Select argument position 3 of F (the counter)
- Check: S(n) ▷ n (strict subterm containment)
- The step argument Y is never evaluated

This is structurally identical to DP on the step-duplicating schema because
the schema has a single defined symbol with a single recursive call site.
On more complex systems with multiple defined symbols or multiple recursive
calls, the two methods diverge: DP extracts marked pair symbols and builds
a dependency graph, while direct counter-projection operates on the original
symbol's argument positions.

The underlying rank is the same `ProjectionRank` as DP. What differs is
the soundness license: the subterm criterion is applied directly to the
rule's argument positions, not to dependency-pair symbols.
-/

namespace OperatorKO7.ConfessionMethodFamily

open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.CompositionalImpossibility

/-- A direct subterm-projection witness on the original recursive symbol.
    On the step-duplicating schema, the only descent-bearing coordinate is the
    third argument, i.e. the recursion counter. -/
structure DirectCounterProjectionWitness where
  selectedCoordinate : Fin 3
  selectedCoordinate_is_counter : selectedCoordinate = ⟨2, by decide⟩

/-- The schema's direct counter-projection witness: select the third argument
    of the recursive call. -/
def schemaDirectCounterProjectionWitness : DirectCounterProjectionWitness where
  selectedCoordinate := ⟨2, by decide⟩
  selectedCoordinate_is_counter := rfl

/-- Route-local rank extracted from direct counter projection.
    This is the "follow the counter, ignore the wrapper" measure obtained from
    the direct subterm-criterion reading of the original recursive symbol. -/
@[simp] def counterProjectionRankFn : Trace → Nat
  | void        => 0
  | delta t     => counterProjectionRankFn t + 1
  | integrate _ => 0
  | merge _ _   => 0
  | app _ _     => 0
  | recΔ _ _ n  => counterProjectionRankFn n
  | eqW _ _     => 0

/-- The direct counter-projection route independently recovers the same
    counter-depth rank function as the DP route. -/
theorem counterProjectionRankFn_eq_dpProjection :
    counterProjectionRankFn = dpProjection := by
  funext t
  induction t <;> simp [counterProjectionRankFn, dpProjection, *]

/-- The direct counter-projection witness packaged as the intermediate
    confession-core witness. -/
def DirectCounterProjectionWitness.toConfessionCoreWitness
    (_W : DirectCounterProjectionWitness) : ConfessionCoreWitness ko7Schema where
  rank := counterProjectionRankFn
  rank_base := by rfl
  rank_succ := by intro t; rfl
  rank_wrap := by intro x y; rfl
  rank_recur := by intro b s n; rfl

/-- The projection rank derived from the direct counter-projection witness. -/
def counterProjectionDerivedRank : ProjectionRank ko7Schema where
  rank := counterProjectionRankFn
  rank_base := by rfl
  rank_succ := by intro t; rfl
  rank_wrap := by intro x y; rfl
  rank_recur := by intro b s n; rfl

/-- The direct counter-projection route converges to the same rank function as
    the canonical DP projection core. -/
theorem counterProjectionDerivedRank_eq_dp_core :
    counterProjectionDerivedRank.rank = dpProjectionRank.rank := by
  simpa [counterProjectionDerivedRank, dpProjectionRank] using
    counterProjectionRankFn_eq_dpProjection

/-- The direct counter-projection route induces the same projection-rank
    structure as the canonical DP core. -/
theorem counterProjectionDerivedRank_eq_dpProjectionRank :
    counterProjectionDerivedRank = dpProjectionRank := by
  ext t
  simpa [counterProjectionDerivedRank, dpProjectionRank] using
    congrFun counterProjectionRankFn_eq_dpProjection t

/-- The direct counter-projection witness forgets the wrapper payload at the
    level of the intermediate confession core. -/
theorem directCounterProjectionWitness_forgets_wrapper_payload :
    ∀ x y : Trace,
      schemaDirectCounterProjectionWitness.toConfessionCoreWitness.rank (app x y) = 0 := by
  intro x y
  rfl

/-- The direct counter-projection witness induces the same confession core as
    the canonical DP route. -/
theorem directCounterProjectionWitness_toConfessionCoreWitness_eq_core :
    schemaDirectCounterProjectionWitness.toConfessionCoreWitness.toProjectionRank =
      dpProjectionRank := by
  ext t
  simpa [DirectCounterProjectionWitness.toConfessionCoreWitness, dpProjectionRank] using
    congrFun counterProjectionRankFn_eq_dpProjection t

/-- Counter-projection via direct subterm criterion on argument position 3.
    Same rank as DP on this schema, but now via an explicit route-local
    witness and derived projection rank rather than direct aliasing. -/
def counterProjectionConfession : ConfessionMethod ko7Schema where
  toProjectionRank := counterProjectionDerivedRank
  license := SoundnessLicense.subtermCriterionDirect

/-- The exported confession instance is genuinely routed through the derived
    counter-projection rank. -/
theorem counterProjectionConfession_is_derived :
    counterProjectionConfession.toProjectionRank = counterProjectionDerivedRank := rfl

/-- On the step-duplicating schema, counter-projection and DP produce the
    same rank function. This is a theorem, not a coincidence: the schema
    has exactly one recursive call with exactly one strictly decreasing
    argument, so every method that extracts the recursive-call structure
    and finds the descent coordinate will find the same coordinate. -/
theorem counterProjection_eq_dp_rank :
    counterProjectionConfession.rank = dpConfession.rank := by
  simpa [counterProjectionConfession, dpConfession, dpProjectionRank,
    counterProjectionDerivedRank] using counterProjectionRankFn_eq_dpProjection

/-- The direct counter-projection witness directly satisfies the generic
    semantic confession profile. -/
theorem directCounterProjectionWitness_has_semantic_profile :
    NormalizedAtBase ko7Schema schemaDirectCounterProjectionWitness.toConfessionCoreWitness.rank
    ∧ TracksSuccessorDepth ko7Schema schemaDirectCounterProjectionWitness.toConfessionCoreWitness.rank
    ∧ ForgetsWrapperPayload ko7Schema schemaDirectCounterProjectionWitness.toConfessionCoreWitness.rank
    ∧ FollowsRecursiveCounter ko7Schema schemaDirectCounterProjectionWitness.toConfessionCoreWitness.rank := by
  exact schemaDirectCounterProjectionWitness.toConfessionCoreWitness.satisfies_semantic_profile

end OperatorKO7.ConfessionMethodFamily
