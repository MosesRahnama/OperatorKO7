# OperatorKO7

This README is a repository map.  
It is intentionally file-descriptive and does not present theorem or benchmark claims.

## Build

```bash
git clone https://github.com/MosesRahnama/OperatorKO7.git
cd OperatorKO7
lake update
lake exe cache get
lake build
```

Toolchain/dependency pins are in:
- `lean-toolchain`
- `lakefile.lean`
- `lake-manifest.json`

## Top-Level Layout

- `OperatorKO7.lean`: library entrypoint imports.
- `OperatorKO7/`: Lean source tree.
- `Artifacts/`: external tool artifacts.
- `Paper/`: manuscript source and paper-related material.
- `Comments/`: notes, review logs, and working records.
- `Docs/`: supplemental documentation files.
- `OperatorKO7_Complete_Documentation.md`: extended file-level map.

## Lean Source Layout

### Core

- `OperatorKO7/Kernel.lean`:
  core term syntax (`Trace`), kernel root relation (`Step`), and closures (`StepStar`).

### Meta Modules

- `OperatorKO7/Meta/SafeStep_Core.lean`:
  `weight`, `kappaM`, `deltaFlag`, guarded `SafeStep` relation.
- `OperatorKO7/Meta/ComputableMeasure.lean`:
  `tau`, `Lex3c`, per-rule decrease (`drop_R_*_c`), `wf_SafeStepRev_c`.
- `OperatorKO7/Meta/ComputableMeasure_Verification.lean`:
  sanity checks: `deltaFlag_binary`, `no_infinite_safestep_chain`.
- `OperatorKO7/Meta/Normalize_Safe.lean`:
  certified normalizer (`WellFounded.fix`); totality and soundness proofs.
- `OperatorKO7/Meta/SafeStep_Ctx.lean`:
  partial context closure `SafeStepCtx` and star lifting lemmas.
- `OperatorKO7/Meta/ContextClosed_SN.lean`:
  `ctxFuel` exponential-weight measure; `wf_SafeStepCtxRev` (unconditional SN).
- `OperatorKO7/Meta/Confluence_Safe.lean`:
  local-join lemmas; `localJoin_all_safe`.
- `OperatorKO7/Meta/Newman_Safe.lean`:
  Newman instantiation; `confluentSafe`, unique normal forms.
- `OperatorKO7/Meta/Impossibility_Lemmas.lean`:
  machine-checked failed-measure catalog.
- `OperatorKO7/Meta/Conjecture_Boundary.lean`:
  no-go theorems, `GlobalOrients` framework.
- `OperatorKO7/Meta/CompositionalMeasure_Impossibility.lean`:
  impossibility theorems (Tier 1 and Tier 2), DP escape clause, `GlobalOrients` bridge.
- `OperatorKO7/Meta/RecCore.lean`:
  RecΔ-core (4 constructors); impossibility restated on minimal sub-signature.
- `OperatorKO7/Meta/DM_OrderType.lean`:
  DM-to-ordinal embedding; ε₀ bridge; per-step strictness; upper-bound calibration.
- `OperatorKO7/Meta/DM_OrderType_LowerBound.lean`:
  `CNFωω` canonical carrier; surjectivity below ω^ω, reflection, rank bridge.
- `OperatorKO7/Meta/Operational_Incompleteness.lean`:
  probe predicates (P1–P3), `InternallyDefinableMeasure`.
- `OperatorKO7/Meta/LinearRec_Ablation.lean`:
  linear recursor variant; `simpleSize` orientation (ablation).
- `OperatorKO7/Meta/MPO_FullStep.lean`:
  MPO orientation of all 8 full-kernel rules (`mpo_orients_step`).
- `OperatorKO7/Meta/HydraCore.lean`:
  toy hydra duplication relation; stress-test encoding for `Operational_Incompleteness`.
- `OperatorKO7/Meta/GoodsteinCore.lean`:
  toy Goodstein base-change relation; stress-test encoding for `Operational_Incompleteness`.

### Tests

- `OperatorKO7/Test/Sanity.lean`:
  basic compilation/evaluation checks.

### Legacy

- `OperatorKO7/Legacy/`:
  archived Lean files retained for reference.

## Artifact Folders

- `Artifacts/ttt2/`:
  TRS input, CPF outputs, and certification logs.

## Paper Folder

- `Paper/Rahnama_KO7_Submission.tex`: manuscript source.
- `Paper/references.bib`: bibliography source.
