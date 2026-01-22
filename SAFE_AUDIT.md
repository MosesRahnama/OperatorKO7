# Scope audit for the KO7 Lean artifact (SafeStep fragment)

This document records a source-linked scope audit against the internal "Strict Execution Contract"
(items A-G) used during development of the `OperatorKO7` Lean formalization.

Scope:
- Positive, certified results are for the guarded relation `SafeStep` (defined in
  `OperatorKO7/Meta/Termination_KO7.lean`).
- The full kernel relation `Step` (defined in `OperatorKO7/Kernel.lean`) is referenced only to
  state explicit caveats (no full-kernel termination or confluence claim is made here).

## Contract items (A-G): evidence pointers

The following pointers are intended for readers/reviewers who want to locate the corresponding
formal statements in the repository.

- A) Branch realism ("rfl gate"):
  - `OperatorKO7/Meta/Operational_Incompleteness.lean` (namespace `OperatorKO7.OpIncomp`), P1 block.
  - Exhibits clause-by-clause analysis for pattern-matched definitions, including explicit
    counterexamples to over-strong global equalities.

- B) Duplication realism:
  - `OperatorKO7/Meta/Operational_Incompleteness.lean` contains the P2 duplication probe, including
    the standard additive non-decrease identity for duplicating rules and the DM/MPO orientation
    premise ("each RHS piece is strictly below the removed LHS redex" in a base order).

- C/D) Symbol realism (NameGate/TypeGate):
  - `OperatorKO7/Meta/Operational_Incompleteness.lean` includes examples illustrating:
    - one successful reference to an existing lemma/tool,
    - one unknown identifier example (kept as documentation-only),
    - one arity/type-mismatch example (kept as documentation-only).

- E) Lexicographic proof discipline:
  - `OperatorKO7/Meta/Termination_KO7.lean` proves per-rule decrease for `SafeStep` via the KO7
    triple-lex order `Lex3` on the measure `μ3`.
  - The decrease proof is structured by explicit case splits corresponding to the safe rules.

- F) Explicit full-kernel caveat (eqW overlap):
  - `OperatorKO7/Meta/Confluence_Safe.lean` proves
    `MetaSN_KO7.not_localJoinStep_eqW_void_void : ¬ LocalJoinStep (eqW void void)`.
  - This records that the two `eqW` kernel rules overlap at `eqW a a`; this is one of the reasons
    the certified artifact is presented for the guarded fragment.

- G) Probes are build-participating and sorry-free:
  - The probe modules and the certified artifact modules are included in the normal import surface.

## Artifact components (reader map)

- Kernel syntax and full kernel step relation:
  - `OperatorKO7/Kernel.lean` (`Trace`, `Step`, `StepStar`, `NormalForm`)

- Safe fragment and termination (ordinal-based):
  - `OperatorKO7/Meta/Termination_KO7.lean` (`SafeStep`, `SafeStepRev`, `μ3`, `Lex3`,
    `measure_decreases_safe`, `wf_SafeStepRev`)

- Certified normalizer (safe fragment):
  - `OperatorKO7/Meta/Normalize_Safe.lean` (`normalizeSafe` plus certificates `to_norm_safe`,
    `norm_nf_safe`); `normalizeSafe` is `noncomputable` because it is defined via well-founded
    recursion on the termination measure.

- Computable termination measure (safe fragment):
  - `OperatorKO7/Meta/ComputableMeasure.lean` and verification helpers under `Meta/ComputableMeasure_*`.

## Paper-code alignment (salient points)

- The recursion successor rule is `recΔ b s (delta n) → app s (recΔ b s n)`; it does not duplicate
  its arguments. The `deltaFlag` component is used to enforce the intended phase decrease for this
  rule in the KO7 triple-lex ordering.

- The multiset component `κᴹ` (`kappaM`) uses multiset union (`∪`) at `merge`/`app`/`eqW` nodes.
  This design is used in the DM branches of the termination proof.

## Build status (informational)

At the time of preparation, the project builds with `lake build` in an environment where the
required dependencies are already available locally.
