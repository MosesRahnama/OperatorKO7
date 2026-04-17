import OperatorKO7.Meta.StepDuplicatingSchema

/-!
# Confession Methods: Generic Interface

A **confession method** on a step-duplicating schema is any termination argument
that extracts a recursive-call relation from the rule structure, projects to a
descent coordinate (the counter), and declares the payload dimension inert under
an external soundness metatheorem.

Formally, this is captured by a `ProjectionRank` (already defined in
`StepDuplicatingSchema.lean`) together with a named soundness justification.
This module wraps that into a `ConfessionMethod` structure and proves that every
`ConfessionMethod` yields orientation and sensitivity-violation properties
inherited from the underlying `ProjectionRank`.
-/

namespace OperatorKO7.ConfessionMethodFamily

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema

/-- The external soundness theorem that licenses the confession.
    Each confession method names a different one. -/
inductive SoundnessLicense
  | artsGiesl2000            -- dependency pairs + subterm criterion
  | subtermCriterionDirect   -- subterm criterion without DP extraction
  | leeJonesBenAmram2001     -- size-change termination
  | argumentFilteringSoundness -- argument filtering within DP framework
  deriving DecidableEq, Repr

/-- A confession method on a step-duplicating schema: a projection rank
    together with the name of the external soundness license that
    justifies dropping the payload dimension. -/
structure ConfessionMethod (S : StepDuplicatingSchema) extends
    ProjectionRank S where
  license : SoundnessLicense

/-- Every confession method orients the duplicating step.
    This follows directly from the `ProjectionRank` orientation theorem. -/
theorem confession_orients {S : StepDuplicatingSchema} (C : ConfessionMethod S)
    (b s n : S.T) :
    C.rank (S.wrap s (S.recur b s n)) < C.rank (S.recur b s (S.succ n)) :=
  projection_orients_dup_step C.toProjectionRank b s n

/-- Every confession method violates wrapper sensitivity on the first argument.
    This is the formal content of "the payload is not tracked." -/
theorem confession_violates_wrap1 {S : StepDuplicatingSchema} (C : ConfessionMethod S) :
    ∃ x y : S.T, ¬ (C.rank (S.wrap x y) > C.rank x) :=
  projection_violates_wrap_subterm1 C.toProjectionRank

/-- Every confession method violates wrapper sensitivity on the second argument. -/
theorem confession_violates_wrap2 {S : StepDuplicatingSchema} (C : ConfessionMethod S) :
    ∃ x y : S.T, ¬ (C.rank (S.wrap x y) > C.rank y) :=
  projection_violates_wrap_subterm2 C.toProjectionRank

end OperatorKO7.ConfessionMethodFamily
