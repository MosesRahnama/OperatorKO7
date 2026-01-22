# KO7 safe audit - strict gates report (concise)

This file records a compact, source-linked audit against the STRICT EXECUTION CONTRACT (A–G) for the current state of KO7. It is scoped to SafeStep unless stated, and uses exact lemma names as in the repo.

## requirements checklist

- P1 rfl-gate (branch realism): Implemented in `OperatorKO7/Meta/Operational_Incompleteness.lean` (namespace `OperatorKO7.OpIncomp`, P1). It enumerates clauses, checks rfl per-branch, and gives a minimal counterexample for the over-strong global law. Status: Done.
- P2 duplication realism: Additive non-drop shown; robust orientations given via DM and MPO examples in `Operational_Incompleteness.lean` and `Operational_Incompleteness_Skeleton.lean` with “every RHS piece < LHS redex” premises. Status: Done.
- P3 symbol realism: One success, one unknown id, and one arity/type mismatch are demonstrated (with unsafe ones kept commented to preserve green build). Status: Done.
- KO7 per-rule decreases (SafeStep): Lex3 drops provided in `Meta/Termination_KO7.lean`; δ-phase for rec_succ; μ/κᴹ branches elsewhere. Status: Done.
- Unguarded KO7 drops added: `drop_R_eq_refl`, `drop_R_merge_cancel` implemented with κ-branching and DM lift helper `dm_to_LexDM_left`. Status: Done.
- Hybrid bridge: `hybrid_R_eq_refl` and `hybrid_R_merge_cancel` now prefer KO7 path when available. Status: Done.
- Newman bridge (SafeStep): `Meta/Newman_Safe.lean` exposes star–star join and `newman_safe`; confluence is derived under local join assumptions. Status: Done for SafeStep.
- Full Step caveat: `Meta/Confluence_Safe.lean` proves `MetaSN_KO7.not_localJoinStep_eqW_void_void`, showing the full kernel `Step` is not locally joinable at the overlapping `eqW` peak; no full-Step confluence is claimed. Status: Explicit.
- Normalizer: `Normalize_Safe.lean` provides a total, sound, noncomputable normalizer for SafeStep via well-founded recursion. Status: Done (noncomputable by design).

## gates A–G (evidence pointers)

- A) Branch-by-branch rfl gate: P1 block in `Operational_Incompleteness.lean` with per-clause rfl and counterexample.
- B) Duplication stress test: additive identity recorded; DM and MPO orientations with base-order premises (see `OperatorKO7.OpIncomp.R4DM.dm_orient`, `OperatorKO7.OpIncomp.R4MPO.weight` families).
- C/D) Symbol realism, NameGate/TypeGate: examples in Operational_Incompleteness (*.lean) show one success, one unknown id, and an arity/type mismatch; identifiers are searched and scoped.
- E) Lex proof gate: KO7 Lex3 proofs split on branches; κ ties established where used, else μ drops strictly; δ drops 1→0 at rec_succ.
- F) Stop-the-line triggers: eqW reflexive root when κᴹ(a)=0 marked as non-local-join; no global full-Step confluence claimed.
- G) Required probes P1–P3: implemented and build-participating (sorry-free).

## paper ↔ code sync (salient points)

- rec_succ is `recΔ b s (delta n) → app s (recΔ b s n)` (no duplication). δ-flag handles 1→0 lex drop; paper text reflects this.
- κᴹ uses multiset union (sup) rather than disjoint-sum; justification is now stated in the paper (DM section) and relied on in κ-branches.
- Labels: use `drop_R_*` and `mpo_drop_R_*` as in code.

## quality gates (current)

- Build, Lint/Typecheck: PASS (lake build). Tests are proof-level; repo is sorry-free on import chain used by claims.

## next steps (tracked)

- Explore unification to a single global measure (if feasible); otherwise keep HybridDec as an explicit disjunctive bridge with guarded scope.
- Expand local-join catalog as needed; keep SafeStep scope front-and-center in user docs.
