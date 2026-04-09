import OperatorKO7.Meta.SymbolicComparatorBarrier

/-!
# Explicit KBO-Style Impossibility Corollary

Architectural status: paper-facing renaming layer.
This module is intentionally thin. The substantive mathematical obstruction is
the variable-condition barrier in `Meta/SymbolicComparatorBarrier.lean`
(`not_orients_dup_rule`), which proves once and for all that any comparator
respecting the standard variable condition cannot orient a rule whose right-hand
side strictly increases the count of any variable. The KO7 `rec_succ` rule
duplicates `s` from one occurrence on the LHS to two on the RHS, so the
abstraction applies directly.

This file exists so that the paper can cite a corollary under a *KBO-facing
name* (`no_kbo_orients_ko7_rec_succ`, `no_kbo_orients_ko7_rec_succ_trace`),
rather than forcing every reviewer to translate from the symbolic abstraction
themselves. Concretely, the file contributes:

1. A type alias `KBOStyleOrder := VariableConditionOrder`.
2. Two one-line forwarding theorems (`no_kbo_orients_dup_step`,
   `no_kbo_orients_ko7_rec_succ`) that re-export the abstract obstruction under
   KBO-facing names.
3. One new bridge theorem (`no_kbo_orients_ko7_rec_succ_trace`) that
   lifts the schema-level statement to the concrete `Trace`-level KO7 rule via
   the `instantiate` map from `SymbolicComparatorBarrier`.

Scope note:
- We do not formalize the full Knuth-Bendix order metatheory here.
- Instead, we isolate the single KBO property that matters for this rule:
  the variable condition.
- Any KBO instance therefore induces a value of `KBOStyleOrder` below.
- Readers wanting the actual proof of the obstruction should look at
  `Meta/SymbolicComparatorBarrier.lean`, not at this file.
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

/-- Trace-level bridge for the KO7 `rec_succ` rule: if a concrete comparator on
instantiated schema terms satisfies the standard variable condition there, it
cannot orient the concrete rule instance. -/
theorem no_kbo_orients_ko7_rec_succ_trace
    (gtT : Trace → Trace → Prop) (bT sT nT : Trace)
    (hvar : ∀ {x y : STerm} {v : SchemaVar},
      gtT (instantiate bT sT nT x) (instantiate bT sT nT y) →
        countVar v y ≤ countVar v x) :
    ¬ gtT (Trace.recΔ bT sT (Trace.delta nT)) (Trace.app sT (Trace.recΔ bT sT nT)) := by
  intro hgt
  have hs : countVar SchemaVar.s dupTgt ≤ countVar SchemaVar.s dupSrc := by
    apply hvar (x := dupSrc) (y := dupTgt) (v := SchemaVar.s)
    simpa [instantiate_dupSrc, instantiate_dupTgt] using hgt
  simp [countVar_dupSrc_s, countVar_dupTgt_s] at hs

end OperatorKO7.KBOImpossible
