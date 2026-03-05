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

### Active Meta Modules

- `OperatorKO7/Meta/SafeStep_Core.lean`:
  guarded relation (`SafeStep`), `deltaFlag`, and multiset payload helpers.
- `OperatorKO7/Meta/ComputableMeasure.lean`:
  computable measure stack (`mu3c`), lex orders, and per-rule decrease lemmas.
- `OperatorKO7/Meta/ComputableMeasure_Verification.lean`:
  additional measure-layer checks/examples.
- `OperatorKO7/Meta/Normalize_Safe.lean`:
  safe-star relation, normal-form predicate, normalizer definitions.
- `OperatorKO7/Meta/SafeStep_Ctx.lean`:
  partial context closure relation and star lifting lemmas.
- `OperatorKO7/Meta/ContextClosed_SN.lean`:
  context-closure accessibility and well-foundedness results.
- `OperatorKO7/Meta/Confluence_Safe.lean`:
  local-join constructions for safe relations.
- `OperatorKO7/Meta/Newman_Safe.lean`:
  Newman-style confluence packaging over safe-star.
- `OperatorKO7/Meta/Conjecture_Boundary.lean`:
  boundary-oriented theorem scaffolding/interfaces.
- `OperatorKO7/Meta/CompositionalMeasure_Impossibility.lean`:
  compositional-measure classes, impossibility statements, projection comparison lemmas.
- `OperatorKO7/Meta/Impossibility_Lemmas.lean`:
  additional failure/impossibility lemma collection.
- `OperatorKO7/Meta/Operational_Incompleteness.lean`:
  auxiliary probe predicates/relations.
- `OperatorKO7/Meta/DM_OrderType.lean`:
  ordinal upper-bound calibration layer.
- `OperatorKO7/Meta/DM_OrderType_LowerBound.lean`:
  lower-bound/rank-bridge calibration layer.
- `OperatorKO7/Meta/RecCore.lean`:
  reduced RecΔ-core signature and specialization lemmas.
- `OperatorKO7/Meta/LinearRec_Ablation.lean`:
  linear-recursion ablation definitions/lemmas.
- `OperatorKO7/Meta/HydraCore.lean`:
  auxiliary Hydra-style module.
- `OperatorKO7/Meta/GoodsteinCore.lean`:
  auxiliary Goodstein-style module.

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
