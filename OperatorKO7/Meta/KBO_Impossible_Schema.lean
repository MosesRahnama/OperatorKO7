import OperatorKO7.Meta.SymbolicComparatorBarrier_Schema

/-!
# Explicit KBO-Style Impossibility Corollary: Schema Layer

Schema-facing naming layer over the symbolic variable-condition barrier.

The KO7 trace-level bridge remains in `Meta/KBO_Impossible.lean`.
-/

namespace OperatorKO7.KBOImpossible

open OperatorKO7.SymbolicComparatorBarrier

/-- Minimal KBO-facing abstraction used by the KO7 impossibility corollary.
It is just a symbolic comparator with the standard variable condition. -/
abbrev KBOStyleOrder := VariableConditionOrder

/-- No KBO-style order can orient the duplicating schema step. -/
theorem no_kbo_orients_dup_step (K : KBOStyleOrder) :
    ¬ K.gt dupSrc dupTgt :=
  not_orients_dup_rule K

/-- No KBO-style order exists that orients the duplicating schema step. -/
theorem no_kbo_orients_ko7_rec_succ :
    ¬ ∃ K : KBOStyleOrder, K.gt dupSrc dupTgt :=
  no_symbolic_variable_condition_orients_dup_step

end OperatorKO7.KBOImpossible
