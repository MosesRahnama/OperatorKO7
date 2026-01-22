import OperatorKO7.Meta.ComputableMeasure
import OperatorKO7.Meta.Termination_KO7

/-!
# Quick test that ComputableMeasure works correctly

This file is intentionally lightweight: it is a scratchpad of `example` goals and `#check`s that
exercise the public surface of the computable termination proof for `SafeStep`.

It is not part of the certified artifact itself; it exists to make regressions obvious during local
development (and for reviewers who want a quick sanity pass without reading the full proofs).
-/

namespace OperatorKO7.MetaCM.Test

open OperatorKO7 Trace

open OperatorKO7.MetaCM
open OperatorKO7.MetaSN_KO7

-- Main theorem is available
example : WellFounded SafeStepRev := wf_SafeStepRev_c

-- Measure decreases for each rule
example (t : OperatorKO7.Trace) :
    OperatorKO7.MetaCM.Lex3c
      (OperatorKO7.MetaCM.mu3c OperatorKO7.Trace.void)
      (OperatorKO7.MetaCM.mu3c (OperatorKO7.Trace.integrate (OperatorKO7.Trace.delta t))) :=
  drop_R_int_delta_c t

-- All 8 rules work
#check drop_R_int_delta_c
#check drop_R_merge_void_left_c
#check drop_R_merge_void_right_c
#check drop_R_merge_cancel_c
#check drop_R_rec_zero_c
#check drop_R_rec_succ_c
#check drop_R_eq_refl_c
#check drop_R_eq_diff_c

-- Main aggregator works
#check measure_decreases_safe_c

-- If this file elaborates, the basic API of `ComputableMeasure.lean` is intact.

end OperatorKO7.MetaCM.Test
