import OperatorKO7.SchemaAPI

/-!
Sanity check: every newly re-exported schema-level module is reachable
through a single `import OperatorKO7.SchemaAPI`. This file exists only
to fail at elaboration time if any of the imports gets dropped from
the public API.
-/

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema

section SchemaAPIReach

-- Core
example : ∀ {S : StepDuplicatingSchema} (M : AdditiveMeasure S),
    ¬ (∀ b s n, M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) :=
  @no_additive_orients_dup_step

-- Tropical continuation
example : @OperatorKO7.StepDuplicating.StepDuplicatingSchema.no_tropical_primary_orients_dup_step_of_unbounded = @no_tropical_primary_orients_dup_step_of_unbounded := rfl

-- Max-aggregative depth barrier (Category C)
example : @no_maxDepth_orients_dup_step = @no_maxDepth_orients_dup_step := rfl

-- Affine-bound sharpness
example : True := by
  have := @OperatorKO7.StepDuplicating.affineThresholdMeasure_bound
  trivial

-- Matrix projection coverage
example : True := by
  have := @no_matrix_orients_dup_step_of_fixed_row_pump
  trivial

-- Second schema instance
example : True := by
  have := @OperatorKO7.TextbookDupInstance.textbookSchema
  trivial

-- SCC utilities
example : True := by
  have := @OperatorKO7.MutualDuplicationCycleFlow.no_global_orients_ctx_additive
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationPayloadFlow.no_global_orients_ctx_additive
  trivial

-- Graph utilities
example : True := by
  have := @OperatorKO7.GraphPathExtraction.EdgePath
  trivial

-- DP fragment
example : True := by
  have := @OperatorKO7.DependencyPairsFragment.DPProjection.wfRev
  trivial

end SchemaAPIReach
