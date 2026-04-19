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

example : True := by
  have := @OperatorKO7.InformationAccess.PrimitiveDuplicatorTerm.live_computation_vs_terminal_record
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.object_undecidability_not_valid_supervisory_verdict
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.InternalMetaHaltClaim
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.ValidSupervisoryMetaHalt
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.supervisory_no_internal_metahalt
  trivial

end SchemaExtendedAPIReach
