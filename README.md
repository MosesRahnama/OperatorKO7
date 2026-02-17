# OperatorKO7

[![Build Status](https://github.com/MosesRahnama/OperatorKO7/actions/workflows/build.yml/badge.svg)](https://github.com/MosesRahnama/OperatorKO7/actions/workflows/build.yml)
[![DOI](https://zenodo.org/badge/DOI/10.48550/arXiv.2512.00081.svg)](https://doi.org/10.48550/arXiv.2512.00081)
[![arXiv](https://img.shields.io/badge/arXiv-2512.00081-b31b1b.svg)](https://arxiv.org/abs/2512.00081)
[![License](https://img.shields.io/badge/License-Dual%20(Academic%20Free%20%7C%20Commercial%20Paid)-green.svg)](LICENSE)

Lean 4 formalization accompanying: [arXiv:2512.00081](https://arxiv.org/abs/2512.00081)

**Contact:** moses.rahnama@gmail.com

## What this repository contains

A mechanically verified Lean 4 development for the KO7 term rewriting system (7 constructors, 8 rules). All theorems compile with zero `sorry`, `admit`, or `axiom` declarations.

### Verified results

| Result | File | Status |
|--------|------|--------|
| Strong normalization (`SafeStep`) | [`Termination_KO7.lean`](OperatorKO7/Meta/Termination_KO7.lean) | Proved |
| Certified normalizer (total + sound) | [`Normalize_Safe.lean`](OperatorKO7/Meta/Normalize_Safe.lean) | Proved |
| Newman confluence engine (`SafeStep`) | [`Newman_Safe.lean`](OperatorKO7/Meta/Newman_Safe.lean) | Proved (parameterized by `locAll`) |
| Non-local-join witness (`eqW void void`) | [`Confluence_Safe.lean`](OperatorKO7/Meta/Confluence_Safe.lean) | Proved |
| Impossibility lemmas (additive/polynomial) | [`Impossibility_Lemmas.lean`](OperatorKO7/Meta/Impossibility_Lemmas.lean) | Proved |
| Conjecture boundary barriers (full-Step no-go families) | [`Conjecture_Boundary.lean`](OperatorKO7/Meta/Conjecture_Boundary.lean) | Proved |

### Scope

- All SN and normalizer results are for the guarded `SafeStep` fragment, not the full `Step` relation.
- The Newman theorem is parameterized by a global local-join hypothesis (`locAll : forall a, LocalJoinAt a`). Confluence follows when that hypothesis is supplied.
- Full-system termination and full-system confluence are **not claimed**.

For a detailed scope audit, see [`SAFE_AUDIT.md`](SAFE_AUDIT.md).

## Kernel definition

[`OperatorKO7/Kernel.lean`](OperatorKO7/Kernel.lean) defines:
- `Trace`: 7 constructors (`void`, `delta`, `integrate`, `merge`, `app`, `recΔ`, `eqW`)
- `Step`: 8 reduction rules
- `StepStar`: reflexive-transitive closure
- `NormalForm`: absence of outgoing steps

## Build

### Prerequisites
- [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (version in `lean-toolchain`)
- Lake (included with Lean)

### Steps

```bash
git clone https://github.com/MosesRahnama/OperatorKO7.git
cd OperatorKO7
elan override set leanprover/lean4:v4.22.0-rc4
lake update
lake exe cache get    # optional, speeds up build
lake build
```

Building without cache may take 30-60 minutes (mathlib compiled from source).

### Reproducibility

- **Lean version:** `v4.22.0-rc4` (pinned in `lean-toolchain`)
- **Dependencies:** locked in `lake-manifest.json`
- **CI:** GitHub Actions on Ubuntu ([build log](https://github.com/MosesRahnama/OperatorKO7/actions/workflows/build.yml))

## File map

### Core

| File | Contents |
|------|----------|
| `OperatorKO7/Kernel.lean` | `Trace`, `Step`, `StepStar`, `NormalForm` |
| `OperatorKO7.lean` | Library entry point (umbrella imports) |

### Meta-theory (`OperatorKO7/Meta/`)

| File | Contents |
|------|----------|
| `Termination.lean` | Ordinal measure toolkit |
| `Termination_KO7.lean` | `SafeStep` definition + SN proof (triple-lex measure) |
| `ComputableMeasure.lean` | Computable termination certificate |
| `Normalize_Safe.lean` | Certified normalizer (total + sound) |
| `Newman_Safe.lean` | Newman engine (parameterized by `locAll`) |
| `Confluence_Safe.lean` | Local-join lemmas + full-step non-join witness |
| `Conjecture_Boundary.lean` | Theorem-level no-go boundaries for internal/full-Step orientation classes |
| `SafeStep_Ctx.lean` | Context-closure utilities |
| `Impossibility_Lemmas.lean` | Failure witnesses for additive/polynomial measures |
| `Operational_Incompleteness.lean` | Operational incompleteness probes (P1-P3) |
| `ContractProbes.lean` | Auxiliary probes |
| `FailureModes.lean` | Counterexample sketches |
| `DM_MPO_Orientation.lean` | DM/MPO orientation helpers |
| `CNFOrdinal.lean` | Ordinal/CNF support |
| `GoodsteinCore.lean` | Goodstein-style toy core |
| `HydraCore.lean` | Hydra-style toy core |
| `ComputableMeasure_Test.lean` | Smoke tests |
| `ComputableMeasure_Verification.lean` | Extra verification lemmas |

### Tests

| File | Contents |
|------|----------|
| `OperatorKO7/Test/Sanity.lean` | Minimal compilation test |

### Paper and configuration

| File | Contents |
|------|----------|
| `CITATION.cff` | Citation metadata |
| `LICENSE` | Dual license (academic free / commercial paid) |
| `lean-toolchain` | Lean version pin |
| `lakefile.lean` | Lake package config |
| `lake-manifest.json` | Dependency lockfile |
| `.github/workflows/build.yml` | CI workflow |

## Citation

```bibtex
@article{rahnama2024operatorko7,
  author       = {Rahnama, Moses},
  title        = {{Strong Normalization for the Safe Fragment of a Minimal
                   Rewrite System: A Triple-Lexicographic Proof and a Conjecture
                   on the Unprovability of Full Termination for Any Relational
                   Operator-Only TRS}},
  journal      = {arXiv preprint arXiv:2512.00081},
  year         = {2024},
  url          = {https://arxiv.org/abs/2512.00081},
  doi          = {10.48550/arXiv.2512.00081}
}
```

## Licensing

- **Lean code**: Dual license (see [`LICENSE`](LICENSE))
  - **Academic / non-commercial use**: Free. Requires citation of arXiv:2512.00081.
  - **Commercial use**: Requires a paid license. Contact moses.rahnama@live.com.
- **Paper text**: CC BY-NC-ND 4.0 (see [`Paper/LICENSE`](Paper/LICENSE))
