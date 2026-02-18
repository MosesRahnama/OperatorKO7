import OperatorKO7.Kernel
import OperatorKO7.Meta.Normalize_Safe
import OperatorKO7.Meta.Confluence_Safe
import OperatorKO7.Meta.Newman_Safe
import OperatorKO7.Meta.ComputableMeasure

open OperatorKO7

/-!
Exported API examples - smoke tests for reviewers.
This module should only import stable, published Meta modules and check that
their key symbols exist and typecheck. It contains no new proofs.
-/

example : WellFounded MetaSN_KO7.SafeStepRev := OperatorKO7.MetaCM.wf_SafeStepRev_c

example (t : Trace) : MetaSN_KO7.SafeStepStar t (MetaSN_KO7.normalizeSafe t) :=
  MetaSN_KO7.to_norm_safe t

example (t : Trace) : MetaSN_KO7.NormalFormSafe (MetaSN_KO7.normalizeSafe t) :=
  MetaSN_KO7.norm_nf_safe t

-- Computable μ3c: simple per-rule drop example (merge void t → t) at t = void
example : OperatorKO7.MetaCM.Lex3c
    (OperatorKO7.MetaCM.mu3c OperatorKO7.Trace.void)
    (OperatorKO7.MetaCM.mu3c (OperatorKO7.Trace.merge OperatorKO7.Trace.void OperatorKO7.Trace.void)) := by
  have hδ : MetaSN_KO7.deltaFlag OperatorKO7.Trace.void = 0 := by
    simp [MetaSN_KO7.deltaFlag]
  simpa using OperatorKO7.MetaCM.drop_R_merge_void_left_c OperatorKO7.Trace.void hδ
