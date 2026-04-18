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

/-- Minimal syntactic subterm relation for the direct counter-projection route.
    We only need enough structure to express that the counter argument is a
    strict syntactic subterm of `delta n`. -/
inductive DirectSubterm : Trace → Trace → Prop
  | delta_arg (n : Trace) : DirectSubterm n (delta n)

/-- Richer original-symbol subterm relation on the full KO7 syntax. This keeps
    the direct route local to the original recursive symbol rather than marked
    dependency-pair syntax. -/
inductive OriginalSymbolSubterm : Trace → Trace → Prop
  | delta_arg (n : Trace) : OriginalSymbolSubterm n (delta n)
  | app_left (x y : Trace) : OriginalSymbolSubterm x (app x y)
  | app_right (x y : Trace) : OriginalSymbolSubterm y (app x y)
  | recur_base (b s n : Trace) : OriginalSymbolSubterm b (recΔ b s n)
  | recur_step (b s n : Trace) : OriginalSymbolSubterm s (recΔ b s n)
  | recur_counter (b s n : Trace) : OriginalSymbolSubterm n (recΔ b s n)
  | trans {x y z : Trace} :
      OriginalSymbolSubterm x y →
      OriginalSymbolSubterm y z →
      OriginalSymbolSubterm x z

/-- The direct counter-step witness `n ▷ delta n` is also a witness in the
    richer original-symbol subterm relation. -/
theorem directSubterm_to_originalSymbolSubterm {x y : Trace}
    (h : DirectSubterm x y) : OriginalSymbolSubterm x y := by
  cases h with
  | delta_arg => exact OriginalSymbolSubterm.delta_arg x

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

/-- Richer route-local evidence for direct counter projection. -/
structure DirectCounterProjectionRouteEvidence where
  witness : DirectCounterProjectionWitness
  originalSymbolSubterm :
    ∀ n, DirectSubterm n (delta n)
  counterSubtermInOriginalCall :
    ∀ b s n, OriginalSymbolSubterm n (recΔ b s (delta n))
  payloadSubtermInOriginalCall :
    ∀ b s n, OriginalSymbolSubterm s (recΔ b s (delta n))
  strictSubtermDescent :
    ∀ n, witness.toConfessionCoreWitness.rank (delta n) =
      witness.toConfessionCoreWitness.rank n + 1
  payloadDropped :
    ∀ x y, witness.toConfessionCoreWitness.rank (app x y) = 0

/-- The concrete rich direct counter-projection evidence on KO7. -/
def schemaDirectCounterProjectionRouteEvidence :
    DirectCounterProjectionRouteEvidence where
  witness := schemaDirectCounterProjectionWitness
  originalSymbolSubterm := by
    intro n
    exact DirectSubterm.delta_arg n
  counterSubtermInOriginalCall := by
    intro b s n
    exact OriginalSymbolSubterm.trans
      (OriginalSymbolSubterm.delta_arg n)
      (OriginalSymbolSubterm.recur_counter b s (delta n))
  payloadSubtermInOriginalCall := by
    intro b s n
    exact OriginalSymbolSubterm.recur_step b s (delta n)
  strictSubtermDescent := by
    intro n
    rfl
  payloadDropped := by
    intro x y
    rfl

/-- Forget the direct-counter-projection-specific witness vocabulary and keep
    only the generic schema-semantic profile. -/
def DirectCounterProjectionRouteEvidence.toRouteEvidence
    (E : DirectCounterProjectionRouteEvidence) : RouteEvidence ko7Schema where
  rank := E.witness.toConfessionCoreWitness.rank
  rank_base := E.witness.toConfessionCoreWitness.rank_base
  rank_succ := E.witness.toConfessionCoreWitness.rank_succ
  rank_wrap := E.witness.toConfessionCoreWitness.rank_wrap
  rank_recur := E.witness.toConfessionCoreWitness.rank_recur

/-- The concrete direct counter-projection route evidence packaged through the
    generic adapter. -/
abbrev schemaDirectCounterProjectionGenericRouteEvidence : RouteEvidence ko7Schema :=
  schemaDirectCounterProjectionRouteEvidence.toRouteEvidence

/-- The richer direct counter-projection evidence entails the generic semantic
    profile. -/
theorem directCounterProjectionRouteEvidence_implies_semantic_profile :
    NormalizedAtBase ko7Schema
      schemaDirectCounterProjectionRouteEvidence.witness.toConfessionCoreWitness.rank
    ∧ TracksSuccessorDepth ko7Schema
      schemaDirectCounterProjectionRouteEvidence.witness.toConfessionCoreWitness.rank
    ∧ ForgetsWrapperPayload ko7Schema
      schemaDirectCounterProjectionRouteEvidence.witness.toConfessionCoreWitness.rank
    ∧ FollowsRecursiveCounter ko7Schema
      schemaDirectCounterProjectionRouteEvidence.witness.toConfessionCoreWitness.rank := by
  have h :=
    ConfessionCoreWitness.satisfies_semantic_profile
      schemaDirectCounterProjectionRouteEvidence.witness.toConfessionCoreWitness
  simpa [schemaDirectCounterProjectionRouteEvidence] using h

/-- The direct counter-projection witness directly satisfies the generic
    semantic confession profile. -/
theorem directCounterProjectionWitness_has_semantic_profile :
    NormalizedAtBase ko7Schema schemaDirectCounterProjectionWitness.toConfessionCoreWitness.rank
    ∧ TracksSuccessorDepth ko7Schema schemaDirectCounterProjectionWitness.toConfessionCoreWitness.rank
    ∧ ForgetsWrapperPayload ko7Schema schemaDirectCounterProjectionWitness.toConfessionCoreWitness.rank
    ∧ FollowsRecursiveCounter ko7Schema schemaDirectCounterProjectionWitness.toConfessionCoreWitness.rank := by
  exact schemaDirectCounterProjectionWitness.toConfessionCoreWitness.satisfies_semantic_profile

end OperatorKO7.ConfessionMethodFamily
