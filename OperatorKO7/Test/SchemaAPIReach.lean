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

-- Paper 2 schema-level quantitative layer
example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.per_step_exchange
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.offset_conservation
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.sum_payloads_doubled
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.proof_entropy_nondecreasing
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.counter_unique_retained_coordinate
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.norm_mismatch_pairwise
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.permutation_gauge_symmetry_package
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.inefficiencyCoefficient_unbounded_atTop
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.explicitDescription_linear_gap
  trivial

-- Paper 2 seed-carrier factorization
example : True := by
  have := @OperatorKO7.SchemaSeedCarrier.PayloadObservable.factorization_criterion
  trivial

example : True := by
  have := @OperatorKO7.SchemaSeedCarrier.additiveObservable_not_factors
  trivial

-- Paper 2 schema forgetting witness
example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.ForgettingWitness.ofProjectionRank
  trivial

-- Paper 2 schema operational incompleteness
example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.OperationalIncompleteness.ofProjectionRank
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.construction_confession_exclusive
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.directAggregationQuestion_operationallyIncomplete
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.canonical_operational_instance
  trivial

-- Paper 2 schema witness order
example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.SchemaWitnessTower.OB_iff_no_directWhole
  trivial

end SchemaAPIReach
