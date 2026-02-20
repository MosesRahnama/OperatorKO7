# OperatorKO7

[![Build Status](https://github.com/MosesRahnama/OperatorKO7/actions/workflows/build.yml/badge.svg)](https://github.com/MosesRahnama/OperatorKO7/actions/workflows/build.yml)
[![DOI](https://zenodo.org/badge/DOI/10.48550/arXiv.2512.00081.svg)](https://doi.org/10.48550/arXiv.2512.00081)
[![arXiv](https://img.shields.io/badge/arXiv-2512.00081-b31b1b.svg)](https://arxiv.org/abs/2512.00081)
[![License](https://img.shields.io/badge/License-Dual%20(Academic%20Free%20%7C%20Commercial%20Paid)-green.svg)](LICENSE)

Lean 4 formalization (~6,400 LOC) for the KO7 rewrite calculus (7 constructors, 8 rules). Zero `sorry`, `admit`, or `axiom`.

**Paper:** [arXiv:2512.00081](https://arxiv.org/abs/2512.00081)
**Contact:** moses.rahnama@gmail.com

## Verified results

| Result | Key file(s) | Status |
|--------|-------------|--------|
| Strong normalization (`SafeStep`) | [`ComputableMeasure.lean`](OperatorKO7/Meta/ComputableMeasure.lean), [`SafeStep_Core.lean`](OperatorKO7/Meta/SafeStep_Core.lean) | Proved |
| Certified normalizer (total + sound) | [`Normalize_Safe.lean`](OperatorKO7/Meta/Normalize_Safe.lean) | Proved |
| Newman confluence (`SafeStep`) | [`Newman_Safe.lean`](OperatorKO7/Meta/Newman_Safe.lean) | Proved (unconditional via `confluentSafe`) |
| Local-join library + non-join witness | [`Confluence_Safe.lean`](OperatorKO7/Meta/Confluence_Safe.lean), [`SafeStep_Ctx.lean`](OperatorKO7/Meta/SafeStep_Ctx.lean) | Proved |
| Impossibility barriers (12 machine-checked + 2 meta-theoretical) | [`Conjecture_Boundary.lean`](OperatorKO7/Meta/Conjecture_Boundary.lean), [`Impossibility_Lemmas.lean`](OperatorKO7/Meta/Impossibility_Lemmas.lean) | Proved |

All SN, normalizer, and confluence results are for the guarded `SafeStep` fragment. Full-system termination is not claimed.

## Build

```bash
git clone https://github.com/MosesRahnama/OperatorKO7.git
cd OperatorKO7
lake update
lake exe cache get    # optional, speeds up build
lake build
```

- **Lean:** `v4.22.0-rc4` (pinned in `lean-toolchain`)
- **Dependencies:** locked in `lake-manifest.json`
- **CI:** [GitHub Actions](https://github.com/MosesRahnama/OperatorKO7/actions/workflows/build.yml)
- Without cache, building mathlib from source takes 30-60 min.

## File map

### Core

| File | Role |
|------|------|
| [`Kernel.lean`](OperatorKO7/Kernel.lean) | `Trace` (7 constructors), `Step` (8 rules), `StepStar`, `NormalForm` |
| [`OperatorKO7.lean`](OperatorKO7.lean) | Library entry point |

### Meta-theory (`OperatorKO7/Meta/`)

| File | Role |
|------|------|
| [`SafeStep_Core.lean`](OperatorKO7/Meta/SafeStep_Core.lean) | Guarded `SafeStep` relation, `deltaFlag`, `kappaM`, DM utilities |
| [`ComputableMeasure.lean`](OperatorKO7/Meta/ComputableMeasure.lean) | Triple-lex measure `mu3c = (delta, kappaM, tau)`, per-rule drops, `wf_SafeStepRev_c` |
| [`Normalize_Safe.lean`](OperatorKO7/Meta/Normalize_Safe.lean) | Certified normalizer: `normalizeSafe`, totality, soundness, idempotence |
| [`SafeStep_Ctx.lean`](OperatorKO7/Meta/SafeStep_Ctx.lean) | Context closure `SafeStepCtx`, lifting lemmas, ctx-local-join infrastructure |
| [`Confluence_Safe.lean`](OperatorKO7/Meta/Confluence_Safe.lean) | Local-join lemmas per root shape, `localJoin_all_safe` global discharge |
| [`Newman_Safe.lean`](OperatorKO7/Meta/Newman_Safe.lean) | Newman's lemma, `confluentSafe`, unique normal forms |
| [`Conjecture_Boundary.lean`](OperatorKO7/Meta/Conjecture_Boundary.lean) | 14 no-go theorems for internal measure families on full `Step` |
| [`Impossibility_Lemmas.lean`](OperatorKO7/Meta/Impossibility_Lemmas.lean) | Additive, flag, constellation, unchecked-recursion failure witnesses |
| [`Operational_Incompleteness.lean`](OperatorKO7/Meta/Operational_Incompleteness.lean) | Toy calculus, `InternallyDefinableMeasure`, DM/MPO orientation, Goodstein/Hydra simulation |
| [`DM_MPO_Orientation.lean`](OperatorKO7/Meta/DM_MPO_Orientation.lean) | DM/MPO helper wrappers |
| [`FailureModes.lean`](OperatorKO7/Meta/FailureModes.lean) | Countermodels (branch realism, duplication, ordinal right-add) |
| [`ContractProbes.lean`](OperatorKO7/Meta/ContractProbes.lean) | P1-P3 contract probe documentation |
| [`PaperApproachIndex.lean`](OperatorKO7/Meta/PaperApproachIndex.lean) | Compile-time consistency check for paper's impossibility catalog |
| [`CNFOrdinal.lean`](OperatorKO7/Meta/CNFOrdinal.lean) | Constructive CNF ordinal with computable comparison |
| [`HydraCore.lean`](OperatorKO7/Meta/HydraCore.lean) | Toy hydra duplication core |
| [`GoodsteinCore.lean`](OperatorKO7/Meta/GoodsteinCore.lean) | Toy Goodstein base-change core |
| [`ComputableMeasure_Verification.lean`](OperatorKO7/Meta/ComputableMeasure_Verification.lean) | Extended verification suite |
| [`ComputableMeasure_Test.lean`](OperatorKO7/Meta/ComputableMeasure_Test.lean) | Smoke tests |
| [`Examples_Publish.lean`](OperatorKO7/Meta/Examples_Publish.lean) | API smoke tests for reviewers |

### Tests

| File | Role |
|------|------|
| [`Test/Sanity.lean`](OperatorKO7/Test/Sanity.lean) | Minimal `#eval` / `#check` compilation test |

## Citation

```bibtex
@article{rahnama2024operatorko7,
  author  = {Rahnama, Moses},
  title   = {{Strong Normalization for the Safe Fragment of a Minimal
              Rewrite Calculus: A Triple-Lexicographic Proof and a
              Conjecture on Full-Termination Limits for Pure Recursive
              Calculi (PRC)}},
  journal = {arXiv preprint arXiv:2512.00081},
  year    = {2024},
  url     = {https://arxiv.org/abs/2512.00081},
  doi     = {10.48550/arXiv.2512.00081}
}
```

## License

- **Lean code:** Dual license (see [`LICENSE`](LICENSE)). Academic/non-commercial: free with citation. Commercial: paid license, contact moses.rahnama@live.com.
- **Paper text:** CC BY-NC-ND 4.0 (see [`Paper/LICENSE`](Paper/LICENSE))
