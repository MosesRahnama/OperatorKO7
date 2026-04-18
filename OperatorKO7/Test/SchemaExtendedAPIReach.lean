import OperatorKO7.SchemaExtendedAPI

namespace SchemaExtendedAPIReach

open OperatorKO7

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.no_tropical_primary_orients_dup_step_of_unbounded
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.no_matrix_orients_dup_step_of_fixed_row_pump
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationCycleFlow.no_global_orients_ctx_additive
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationPayloadFlow.no_global_orients_ctx_additive
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.additive_witness
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.nat_direct_escape_trichotomy
  trivial

end SchemaExtendedAPIReach
