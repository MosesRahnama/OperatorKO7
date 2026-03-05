# OperatorKO7

This README is a file-level map of the repository.
It does not make theorem or performance claims.

## Build

```bash
git clone https://github.com/MosesRahnama/OperatorKO7.git
cd OperatorKO7
lake update
lake exe cache get
lake build
```

Toolchain and dependency pins are in:
- `lean-toolchain`
- `lakefile.lean`
- `lake-manifest.json`

## Top-Level Files

- [`OperatorKO7.lean`](OperatorKO7.lean): library entrypoint imports.
- [`lakefile.lean`](lakefile.lean): Lake package configuration.
- [`lean-toolchain`](lean-toolchain): Lean version pin.
- [`LICENSE`](LICENSE): repository license text.
- [`OperatorKO7_Complete_Documentation.md`](OperatorKO7_Complete_Documentation.md): generated code dump/documentation.

## Lean Source Layout

### Core

- [`OperatorKO7/Kernel.lean`](OperatorKO7/Kernel.lean):
  `Trace`, `Step`, `StepStar`, `NormalForm`, and basic closure lemmas.

### Active Meta Modules

- [`OperatorKO7/Meta/SafeStep_Core.lean`](OperatorKO7/Meta/SafeStep_Core.lean):
  guarded relation (`SafeStep`), `deltaFlag`, `kappaM`, DM helpers.
- [`OperatorKO7/Meta/ComputableMeasure.lean`](OperatorKO7/Meta/ComputableMeasure.lean):
  computable triple measure (`mu3c`), lex orders, per-rule decrease lemmas.
- [`OperatorKO7/Meta/ComputableMeasure_Verification.lean`](OperatorKO7/Meta/ComputableMeasure_Verification.lean):
  additional checks/examples around the computable measure layer.
- [`OperatorKO7/Meta/Normalize_Safe.lean`](OperatorKO7/Meta/Normalize_Safe.lean):
  `SafeStepStar`, normal-form predicate, normalization function and related lemmas.
- [`OperatorKO7/Meta/SafeStep_Ctx.lean`](OperatorKO7/Meta/SafeStep_Ctx.lean):
  context closure (`SafeStepCtx`) and star lifting utilities.
- [`OperatorKO7/Meta/Confluence_Safe.lean`](OperatorKO7/Meta/Confluence_Safe.lean):
  local-join definitions/lemmas for safe relation plus full-step non-join witness.
- [`OperatorKO7/Meta/Newman_Safe.lean`](OperatorKO7/Meta/Newman_Safe.lean):
  Newman-style confluence packaging on safe-star relation.
- [`OperatorKO7/Meta/Impossibility_Lemmas.lean`](OperatorKO7/Meta/Impossibility_Lemmas.lean):
  catalog-style impossibility/failure witnesses.
- [`OperatorKO7/Meta/Conjecture_Boundary.lean`](OperatorKO7/Meta/Conjecture_Boundary.lean):
  no-go theorem wrappers and `GlobalOrients` interface.
- [`OperatorKO7/Meta/CompositionalMeasure_Impossibility.lean`](OperatorKO7/Meta/CompositionalMeasure_Impossibility.lean):
  compositional-measure classes and barrier/DP-escape statements.
- [`OperatorKO7/Meta/Operational_Incompleteness.lean`](OperatorKO7/Meta/Operational_Incompleteness.lean):
  auxiliary probe language/relation and related scaffolding.
- [`OperatorKO7/Meta/DM_OrderType.lean`](OperatorKO7/Meta/DM_OrderType.lean):
  ordinal upper-bound calibration layer.
- [`OperatorKO7/Meta/DM_OrderType_LowerBound.lean`](OperatorKO7/Meta/DM_OrderType_LowerBound.lean):
  CNF carrier and lower-bound/rank-bridge calibration layer.
- [`OperatorKO7/Meta/LinearRec_Ablation.lean`](OperatorKO7/Meta/LinearRec_Ablation.lean):
  linear-recursion ablation module and comparison lemmas.
- [`OperatorKO7/Meta/HydraCore.lean`](OperatorKO7/Meta/HydraCore.lean):
  small Hydra-style auxiliary core.
- [`OperatorKO7/Meta/GoodsteinCore.lean`](OperatorKO7/Meta/GoodsteinCore.lean):
  small Goodstein-style auxiliary core.

### Test

- [`OperatorKO7/Test/Sanity.lean`](OperatorKO7/Test/Sanity.lean):
  basic compile/eval checks.

### Archived Modules

Archived files are in [`OperatorKO7/Legacy/`](OperatorKO7/Legacy) and are not part of the active `Meta` set.

## TTT2/CeTA Artifacts

[`Artifacts/ttt2/`](Artifacts/ttt2/) contains the termination-tool pipeline:

- `KO7_full_step.trs`: input TRS (8 rules, 7 constructors).
- CPF proof certificates for each YES strategy:
  - `KO7_FAST.cpf`, `KO7_LPO.cpf`, `KO7_COMP.cpf`.
- CPF outputs for MAYBE strategies:
  - `KO7_KBO.cpf`, `KO7_POLY.cpf`, `KO7_MAT2.cpf`, `KO7_MAT3.cpf`.
- `KO7_CeTA_certification.txt`: CeTA 2.36 verification log.

All four modular/structural strategies (FAST, HYDRA, COMP, LPO) are **CeTA CERTIFIED**.
All four global/compositional strategies (KBO, POLY, MAT(2), MAT(3)) are **CeTA REJECTED**.
FBI returned MAYBE with no certifiable output.

## Paper Folder

- [`Paper/Rahnama_KO7_Submission.tex`](Paper/Rahnama_KO7_Submission.tex): manuscript source.
- `Paper/references.bib`: bibliography source.

