import OperatorKO7.Meta.ConfessionMethod
import OperatorKO7.Meta.ConfessionMethod_DP

/-!
# Confession Method Instance: Argument Filtering

Argument filtering (Arts-Giesl 2000, within the DP framework) maps each
function symbol to a subset or projection of its argument list. For the
step-duplicating schema:

- π(recur) = 3   (project to the counter argument only)
- π(wrap) = ε    (collapse to nothing)
- π(succ) = 1    (keep the single argument)
- π(base) = ε    (collapse to nothing)

After filtering, the duplicating rule `recur(b, s, succ(n)) → wrap(s, recur(b, s, n))`
becomes `succ(n) → n` in the filtered universe: the wrapper and the duplicated
payload are entirely absent. Termination of the filtered problem is trivial.

Argument filtering is a **structural drop**: it removes arguments from the
proof obligation rather than constructing a new comparison object. The
soundness is licensed by the argument-filtering soundness theorem within
the DP framework, which guarantees that termination of the filtered problem
implies termination of the original system under the conditions of the
framework.

On the step-duplicating schema, argument filtering produces the same
concrete rank as DP + subterm criterion and counter-projection. What differs
is the extraction mechanism (filtering map rather than DP pair extraction or
direct argument selection) and the specific soundness theorem invoked.
-/

namespace OperatorKO7.ConfessionMethodFamily

open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.CompositionalImpossibility

/-- A route-local argument-filtering witness on the original symbols.
    The filter keeps only the counter coordinate of `recΔ`, drops the wrapper,
    preserves `delta`, and collapses the remaining constructors. -/
structure ArgumentFilteringWitness where
  keepRecurCoordinate : Fin 3
  keepRecurCoordinate_is_counter : keepRecurCoordinate = ⟨2, by decide⟩

/-- The concrete schema witness for argument filtering. -/
def schemaArgumentFilteringWitness : ArgumentFilteringWitness where
  keepRecurCoordinate := ⟨2, by decide⟩
  keepRecurCoordinate_is_counter := rfl

/-- Route-local rank extracted from the filtering view.
    After filtering away the wrapper and duplicated payload, only the counter
    depth remains visible. -/
@[simp] def argumentFilteringRankFn : Trace → Nat
  | void        => 0
  | delta t     => argumentFilteringRankFn t + 1
  | integrate _ => 0
  | merge _ _   => 0
  | app _ _     => 0
  | recΔ _ _ n  => argumentFilteringRankFn n
  | eqW _ _     => 0

/-- The argument-filtering route independently recovers the same counter-depth
    rank function as the DP route. -/
theorem argumentFilteringRankFn_eq_dpProjection :
    argumentFilteringRankFn = dpProjection := by
  funext t
  induction t <;> simp [argumentFilteringRankFn, dpProjection, *]

/-- The argument-filtering witness packaged as the intermediate
    confession-core witness. -/
def ArgumentFilteringWitness.toConfessionCoreWitness
    (_W : ArgumentFilteringWitness) : ConfessionCoreWitness ko7Schema where
  rank := argumentFilteringRankFn
  rank_base := by rfl
  rank_succ := by intro t; rfl
  rank_wrap := by intro x y; rfl
  rank_recur := by intro b s n; rfl

/-- The projection rank derived from argument filtering. -/
def argumentFilteringDerivedRank : ProjectionRank ko7Schema where
  rank := argumentFilteringRankFn
  rank_base := by rfl
  rank_succ := by intro t; rfl
  rank_wrap := by intro x y; rfl
  rank_recur := by intro b s n; rfl

/-- The argument-filtering route converges to the same rank function as the
    canonical DP projection core. -/
theorem argumentFilteringDerivedRank_eq_dp_core :
    argumentFilteringDerivedRank.rank = dpProjectionRank.rank := by
  simpa [argumentFilteringDerivedRank, dpProjectionRank] using
    argumentFilteringRankFn_eq_dpProjection

/-- The argument-filtering route converges to the same projection-rank object
    as the canonical DP route. -/
theorem argumentFilteringDerivedRank_eq_dpProjectionRank :
    argumentFilteringDerivedRank = dpProjectionRank := by
  ext t
  simpa [argumentFilteringDerivedRank, dpProjectionRank] using
    congrFun argumentFilteringRankFn_eq_dpProjection t

/-- The argument-filtering witness forgets the wrapper payload at the level of
    the intermediate confession core. -/
theorem argumentFilteringWitness_forgets_wrapper_payload :
    ∀ x y : Trace,
      schemaArgumentFilteringWitness.toConfessionCoreWitness.rank (app x y) = 0 := by
  intro x y
  rfl

/-- The argument-filtering witness induces the same confession core as the
    canonical DP route. -/
theorem argumentFilteringWitness_toConfessionCoreWitness_eq_core :
    schemaArgumentFilteringWitness.toConfessionCoreWitness.toProjectionRank =
      dpProjectionRank := by
  ext t
  simpa [ArgumentFilteringWitness.toConfessionCoreWitness, dpProjectionRank] using
    congrFun argumentFilteringRankFn_eq_dpProjection t

/-- Argument filtering as a confession method on KO7.
    Same projection rank, but now via an explicit filtering witness and derived
    projection rank; the license is the argument-filtering soundness theorem
    within the DP framework. -/
def argumentFilteringConfession : ConfessionMethod ko7Schema where
  toProjectionRank := argumentFilteringDerivedRank
  license := SoundnessLicense.argumentFilteringSoundness

/-- The exported argument-filtering confession instance is routed through the
    derived argument-filtering rank. -/
theorem argumentFilteringConfession_is_derived :
    argumentFilteringConfession.toProjectionRank = argumentFilteringDerivedRank := rfl

/-- On the step-duplicating schema, argument filtering and DP produce
    the same rank function. -/
theorem argumentFiltering_eq_dp_rank :
    argumentFilteringConfession.rank = dpConfession.rank := by
  simpa [argumentFilteringConfession, dpConfession, argumentFilteringDerivedRank,
    dpProjectionRank] using argumentFilteringRankFn_eq_dpProjection

/-- The filtered counter-only target syntax used by the argument-filtering
    route. -/
inductive FilteredCounterTerm
  | zero : FilteredCounterTerm
  | succ : FilteredCounterTerm → FilteredCounterTerm
  deriving DecidableEq, Repr

/-- The filtered counter-only step semantics. -/
inductive FilteredCounterStep : FilteredCounterTerm → FilteredCounterTerm → Prop
  | succ_step (n : FilteredCounterTerm) : FilteredCounterStep (.succ n) n

/-- The route-local argument filter on KO7 traces:
    - keep the counter through `recΔ`
    - keep the unique argument through `delta`
    - project `app` to its recursive-call payload side
    - reject non-schema constructors. -/
@[simp] def argumentFilterTrace : Trace → Option FilteredCounterTerm
  | void => some FilteredCounterTerm.zero
  | delta t => Option.map FilteredCounterTerm.succ (argumentFilterTrace t)
  | integrate _ => none
  | merge _ _ => none
  | app _ y => argumentFilterTrace y
  | recΔ _ _ n => argumentFilterTrace n
  | eqW _ _ => none

/-- Richer route-local evidence for argument filtering. -/
structure ArgumentFilteringRouteEvidence where
  witness : ArgumentFilteringWitness
  filteredDupLhs :
    ∀ b s n,
      argumentFilterTrace (recΔ b s (delta n)) =
        Option.map FilteredCounterTerm.succ (argumentFilterTrace n)
  filteredDupRhs :
    ∀ b s n,
      argumentFilterTrace (app s (recΔ b s n)) = argumentFilterTrace n
  payloadErased :
    ∀ s n,
      argumentFilterTrace (app s n) = argumentFilterTrace n
  filteredStepShape :
    ∀ b s n m,
      argumentFilterTrace n = some m →
      argumentFilterTrace (recΔ b s (delta n)) = some (FilteredCounterTerm.succ m)
      ∧ argumentFilterTrace (app s (recΔ b s n)) = some m
      ∧ FilteredCounterStep (FilteredCounterTerm.succ m) m

/-- The concrete rich argument-filtering route evidence on KO7. -/
def schemaArgumentFilteringRouteEvidence : ArgumentFilteringRouteEvidence where
  witness := schemaArgumentFilteringWitness
  filteredDupLhs := by
    intro b s n
    rfl
  filteredDupRhs := by
    intro b s n
    rfl
  payloadErased := by
    intro s n
    rfl
  filteredStepShape := by
    intro b s n m hm
    refine ⟨?_, ?_, FilteredCounterStep.succ_step m⟩
    · simp [argumentFilterTrace, hm]
    · simpa [argumentFilterTrace] using hm

/-- The richer argument-filtering evidence entails the generic semantic
    profile. -/
theorem argumentFilteringRouteEvidence_implies_semantic_profile :
    NormalizedAtBase ko7Schema
      schemaArgumentFilteringRouteEvidence.witness.toConfessionCoreWitness.rank
    ∧ TracksSuccessorDepth ko7Schema
      schemaArgumentFilteringRouteEvidence.witness.toConfessionCoreWitness.rank
    ∧ ForgetsWrapperPayload ko7Schema
      schemaArgumentFilteringRouteEvidence.witness.toConfessionCoreWitness.rank
    ∧ FollowsRecursiveCounter ko7Schema
      schemaArgumentFilteringRouteEvidence.witness.toConfessionCoreWitness.rank := by
  have h :=
    ConfessionCoreWitness.satisfies_semantic_profile
      schemaArgumentFilteringRouteEvidence.witness.toConfessionCoreWitness
  simpa [schemaArgumentFilteringRouteEvidence] using h

/-- The argument-filtering witness directly satisfies the generic semantic
    confession profile. -/
theorem argumentFilteringWitness_has_semantic_profile :
    NormalizedAtBase ko7Schema schemaArgumentFilteringWitness.toConfessionCoreWitness.rank
    ∧ TracksSuccessorDepth ko7Schema schemaArgumentFilteringWitness.toConfessionCoreWitness.rank
    ∧ ForgetsWrapperPayload ko7Schema schemaArgumentFilteringWitness.toConfessionCoreWitness.rank
    ∧ FollowsRecursiveCounter ko7Schema schemaArgumentFilteringWitness.toConfessionCoreWitness.rank := by
  exact schemaArgumentFilteringWitness.toConfessionCoreWitness.satisfies_semantic_profile

end OperatorKO7.ConfessionMethodFamily
