import OperatorKO7.Meta.StepDuplicatingSchema
import OperatorKO7.Meta.ConfessionMethod

/-!
# Schema-Generic Forgetting Witness

This module introduces a schema-level `ForgettingWitness S` abstraction and
proves:

1. Every `ProjectionRank S` (and hence every `ConfessionMethod S`) induces a
   `ForgettingWitness S`: a schema-generic rank that orients the duplicating
   step while violating wrapper sensitivity on both payload positions.

2. The KO7 `CertifiedForgettingWitness` defined in
   [`Meta/OperationalIncompleteness.lean`](OperationalIncompleteness.lean) is
   a specialization of the generic structure at `ko7Schema`.

The schema-level forgetting-witness abstraction is the central primitive for
Paper 2's W2 family: all four confession methods (dependency pairs, direct
counter-projection, SCT, argument filtering) collapse to the same
`ProjectionRank S` on a step-duplicating schema and therefore share the same
forgetting-witness data.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-- **Schema-generic forgetting witness.** A rank on a step-duplicating
schema that orients the duplicating step and *explicitly* violates wrapper
sensitivity on each of the two payload positions.

The name "forgetting" reflects that the rank succeeds by discarding the
wrapper context: any direct whole-term barrier family requires
`rank (wrap x y) > rank x` and `rank (wrap x y) > rank y`, but the
wrapper-sensitivity violations here are the formal content of "the rank
forgets the payload". -/
structure ForgettingWitness (S : StepDuplicatingSchema) where
  rank : S.T → Nat
  orientsDupStep :
    ∀ b s n,
      rank (S.wrap s (S.recur b s n))
        < rank (S.recur b s (S.succ n))
  violatesPayloadLeft :
    ∃ x y : S.T, ¬ (rank (S.wrap x y) > rank x)
  violatesPayloadRight :
    ∃ x y : S.T, ¬ (rank (S.wrap x y) > rank y)

namespace ForgettingWitness

/-- **Every `ProjectionRank S` yields a `ForgettingWitness S`.** This is the
schema-generic core of Paper 2's "confession method → certified forgetting"
bridge, replacing the KO7-specific derivation in the current
`OperationalIncompleteness.lean`. -/
def ofProjectionRank {S : StepDuplicatingSchema}
    (R : ProjectionRank S) : ForgettingWitness S where
  rank := R.rank
  orientsDupStep := projection_orients_dup_step R
  violatesPayloadLeft := projection_violates_wrap_subterm1 R
  violatesPayloadRight := projection_violates_wrap_subterm2 R

@[simp] theorem ofProjectionRank_rank {S : StepDuplicatingSchema}
    (R : ProjectionRank S) :
    (ofProjectionRank R).rank = R.rank := rfl

/-- Every confession-core witness also yields a generic forgetting witness,
    by packaging it as the shared projection core first. -/
def ofConfessionCoreWitness {S : StepDuplicatingSchema}
    (W : ConfessionCoreWitness S) : ForgettingWitness S :=
  ofProjectionRank W.toProjectionRank

@[simp] theorem ofConfessionCoreWitness_rank {S : StepDuplicatingSchema}
    (W : ConfessionCoreWitness S) :
    (ofConfessionCoreWitness W).rank = W.rank := rfl

/-- Any rank satisfying the semantic confession-core profile yields a generic
    forgetting witness directly. -/
def ofSemanticProfile {S : StepDuplicatingSchema} (rank : S.T → Nat)
    (hbase : NormalizedAtBase S rank)
    (hsucc : TracksSuccessorDepth S rank)
    (hwrap : ForgetsWrapperPayload S rank)
    (hrecur : FollowsRecursiveCounter S rank) : ForgettingWitness S where
  rank := rank
  orientsDupStep := semanticProfile_orients_dup_step hbase hsucc hwrap hrecur
  violatesPayloadLeft := semanticProfile_violates_wrap_subterm1 hbase hsucc hwrap
  violatesPayloadRight := semanticProfile_violates_wrap_subterm2 hbase hsucc hwrap

@[simp] theorem ofSemanticProfile_rank {S : StepDuplicatingSchema}
    (rank : S.T → Nat)
    (hbase : NormalizedAtBase S rank)
    (hsucc : TracksSuccessorDepth S rank)
    (hwrap : ForgetsWrapperPayload S rank)
    (hrecur : FollowsRecursiveCounter S rank) :
    (ofSemanticProfile rank hbase hsucc hwrap hrecur).rank = rank := rfl

end ForgettingWitness

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating

namespace OperatorKO7.ConfessionMethodFamily

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema

/-- **Every `ConfessionMethod S` yields a `ForgettingWitness S`**, via its
underlying projection rank. -/
def ConfessionMethod.toForgettingWitness
    {S : StepDuplicatingSchema} (C : ConfessionMethod S) :
    ForgettingWitness S :=
  ForgettingWitness.ofProjectionRank C.toProjectionRank

@[simp] theorem ConfessionMethod.toForgettingWitness_rank
    {S : StepDuplicatingSchema} (C : ConfessionMethod S) :
    C.toForgettingWitness.rank = C.rank := rfl

end OperatorKO7.ConfessionMethodFamily
