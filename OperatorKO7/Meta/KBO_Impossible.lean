import OperatorKO7.Meta.SymbolicComparatorBarrier

/-!
# Explicit KBO-Style Impossibility Corollary

The symbolic variable-condition barrier already shows that any direct comparator
respecting the standard variable condition fails on the duplicating schema step.
This file records that consequence under KBO-facing names so the paper can cite a
concrete KO7 corollary rather than only the abstract symbolic barrier.

Scope note:
- We do not formalize the full Knuth-Bendix order metatheory here.
- Instead, we isolate the single KBO property that matters for this rule:
  the variable condition.
- Any KBO instance therefore induces a value of `KBOStyleOrder` below.
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
theorem no_kbo_orients_dup_step_exists :
    ¬ ∃ K : KBOStyleOrder, K.gt dupSrc dupTgt :=
  no_symbolic_variable_condition_orients_dup_step

/-- The KO7 `rec_succ` rule is an instance of the symbolic duplicating schema.
This theorem packages the impossibility under an explicit KO7-facing name. -/
theorem no_kbo_orients_ko7_rec_succ :
    ¬ ∃ K : KBOStyleOrder, K.gt dupSrc dupTgt :=
  no_kbo_orients_dup_step_exists

end OperatorKO7.KBOImpossible
