# OperatorKO7

[![Build Status](https://github.com/MosesRahnama/OperatorKO7/actions/workflows/build.yml/badge.svg)](https://github.com/MosesRahnama/OperatorKO7/actions/workflows/build.yml)
[![DOI](https://zenodo.org/badge/DOI/10.48550/arXiv.2512.00081.svg)](https://doi.org/10.48550/arXiv.2512.00081)
[![arXiv](https://img.shields.io/badge/arXiv-2512.00081-b31b1b.svg)](https://arxiv.org/abs/2512.00081)
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)

**CONJECTURE:** No relational operator-only TRS can have its full-system termination proved by internally definable methods.

**MAIN RESULT:** A mechanically-verified certified normalizer for a guarded fragment (`SafeStep`) using a novel triple-lexicographic measure.

**Paper (arXiv):** [https://arxiv.org/abs/2512.00081](https://arxiv.org/abs/2512.00081)  
**Zenodo Record:** [https://doi.org/10.48550/arXiv.2512.00081](https://doi.org/10.48550/arXiv.2512.00081)  
**Repository:** [https://github.com/MosesRahnama/OperatorKO7](https://github.com/MosesRahnama/OperatorKO7)  
**Contact:** moses.rahnama@live.com

This repository contains the Lean 4 formalization accompanying the paper above.

## Overview (what is proved vs what is conjectured)

### The System: KO7

KO7 is a minimal rewrite calculus with **7 constructors** and **8 reduction rules**. It is deliberately designed as a minimal "relational operator-only" term rewriting system—meaning it can encode ordered computation (comparisons, iteration, sequential counting) using only structural rewrite rules without primitive recursion or arithmetic operators.

### What This Repository Proves (Mechanically Verified)

This repository **formally verifies** in Lean 4:

1. **Safe fragment (`SafeStep`) strong normalization (SN)**: A restricted subset of KO7's reduction rules provably terminates. The proof uses a novel **triple-lexicographic measure** combining:
   - A phase bit (tracks reduction stage)
   - Multiset ordering (Dershowitz-Manna)
   - Ordinal ranking (handles non-additive cases)

2. **Certified normalizer**: A provably-total and provably-sound normalization function for `SafeStep`. Given any term in the safe fragment, it computes the unique normal form.

3. **Confluence (safe fragment)**: Under the assumption of local confluence (verified through critical pair analysis), Newman's Lemma yields confluence, guaranteeing unique normal forms for the safe fragment.

4. **Impossibility catalog**: Machine-checked "no-go" witnesses demonstrating that simpler termination measures **provably fail** for KO7. Specifically:
   - Additive counters fail (term duplication defeats them)
   - Polynomial interpretations fail
   - Single-bit flags fail
   - Any measure based on additive invariants fails

### What This Repository Does NOT Prove (The Conjecture)

This repository **does not** claim a proof of termination for the **full kernel `Step` relation**. The full system includes an additional rule (`eqW`) that redistributes step arguments across recursive calls in a way that defeats all known termination measures.

**The Conjecture** (stated but not proved): 
> No relational operator-only term rewriting system can have its **full-system termination** proved by methods definable within the system itself.

**Why this matters:**
- "Relational" means capable of **ordered computation** (comparison, iteration, counting)
- Such systems necessarily include recursors that **redistribute** computational resources (step counts, fuel) across subterms
- This redistribution **defeats additive measures** (the resource can grow locally even as it shrinks globally)
- The conjecture suggests a **fundamental limitation**: systems expressive enough to encode ordered data cannot prove their own termination using measures they can internally define

**Analogy**: This is similar to Gödel's incompleteness—systems of sufficient expressive power cannot prove all true statements about themselves. Here, we conjecture that rewrite systems expressive enough for relational reasoning cannot prove their own termination using internally definable orderings.

### Evidence for the Conjecture

While the conjecture itself is not formally proved, this repository provides:
- **Constructive proof** that a large safe fragment terminates (establishing partial progress)
- **Machine-checked impossibility results** showing why simpler approaches fail
- **Explicit counterexample** in `Confluence_Safe.lean` demonstrating the non-joinable peak at `eqW` that breaks full termination
- **Operational incompleteness probes** (P1–P3) showing the boundary where internal methods break down

The gap between what is proved (`SafeStep` terminates) and what is conjectured (full `Step` does not provably terminate by internal methods) is **deliberate and explicit**. This work explores the **limits of self-reference in termination proving**.

For a complete scope audit detailing exactly which theorems are proved and which claims remain conjectural, see [`SAFE_AUDIT.md`](SAFE_AUDIT.md).

## Archival and Reproducibility

### Permanent Archive

This work is permanently archived with the following identifiers:

- **Paper DOI:** [10.48550/arXiv.2512.00081](https://doi.org/10.48550/arXiv.2512.00081)
- **arXiv ID:** [2512.00081](https://arxiv.org/abs/2512.00081)
- **Repository (live):** [github.com/MosesRahnama/OperatorKO7](https://github.com/MosesRahnama/OperatorKO7)
- **Zenodo Archive:** [zenodo.org/records/18351560](https://zenodo.org/records/18351560)

### Build Verification

This repository is continuously built and verified via [GitHub Actions CI](https://github.com/MosesRahnama/OperatorKO7/actions/workflows/build.yml). The build status badge above indicates the current verification state.

## Build Instructions

### Prerequisites
- [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (version specified in `lean-toolchain`)
- Lake (Lean's build tool, included with Lean)

### Standard Build

```bash
# Clone the repository
git clone https://github.com/MosesRahnama/OperatorKO7.git
cd OperatorKO7

# Update dependencies
lake update

# Fetch mathlib cache (optional but recommended; significantly speeds up build)
lake exe cache get

# Build the project
lake build
```

### Minimal Build (without cache)

```bash
lake build
```

**Note:** Building without the mathlib cache may take 30-60 minutes depending on your system, as mathlib will be compiled from source.

## Reproducibility

To ensure exact reproducibility of the formalization presented in the paper:

- **Lean version:** `v4.22.0-rc4` (pinned in `lean-toolchain`)
- **Paper version:** November 26, 2025 (v1 on arXiv)
- **Dependencies:** Locked in `lake-manifest.json`
- **Build verification:** Continuously tested on Ubuntu via GitHub Actions
- **Commit hash:** Use the main branch or specific tagged release

### Verifying the Exact Paper Version

```bash
# Clone the repository
git clone https://github.com/MosesRahnama/OperatorKO7.git
cd OperatorKO7

# Build the current version
lake exe cache get
lake build
```

All theorems referenced in the paper are present in the codebase and can be verified by Lake's build process.

## Complete file-by-file guide (every file in this repo)

Every file in this repository exists for one of: (i) the paper source/license, (ii) the Lean kernel, (iii) the certified safe fragment, or (iv) small verifier-facing smoke tests.

### Repo root
- **`README.md`**: this landing page (theory-first, then build instructions, then file map).
- **`SAFE_AUDIT.md`**: reader-facing scope audit: a concise "what is proved vs. what is not" map, with pointers to the exact Lean files/lemmas establishing the SafeStep artifact and the explicit full-kernel caveat.
- **`CITATION.cff`**: machine-readable citation metadata for this software artifact.
- **`ARCHIVAL_STRATEGY.md`**: comprehensive documentation of archival and citation strategy.
- **`RELEASE_GUIDE.md`**: step-by-step guide for creating releases and DOI archival.
- **`LICENSE`**: Apache-2.0 license for the Lean code in this repository.
- **`.gitignore`**: Git ignore patterns (excludes build artifacts).
- **`lean-toolchain`**: pins the Lean toolchain version used to build the project.
- **`lakefile.lean`**: Lake package config (declares package/library `OperatorKO7`, depends on mathlib).
- **`lake-manifest.json`**: Lake dependency lockfile (generated by Lake).
- **`OperatorKO7.lean`**: the library entry point (umbrella imports for the public build surface).

### CI/CD
- **`.github/workflows/build.yml`**: GitHub Actions workflow for continuous integration and build verification.

### Paper
- **`Paper/Rahnama_KO7_Submission.pdf`**: paper source (includes direct link to this repo).
- **`Paper/LICENSE`**: CC BY-NC-ND 4.0 legal code + notice for the paper text.

### Lean library (`OperatorKO7/`)
- **`OperatorKO7/Kernel.lean`**: defines `Trace` (7 constructors), the full kernel relation `Step` (8 unconditional rules), and `StepStar`.

### Lean meta-theory (`OperatorKO7/Meta/`)
- **`OperatorKO7/Meta/Termination.lean`**: ordinal/measure toolkit used by the termination development.
- **`OperatorKO7/Meta/Termination_KO7.lean`**: defines the certified safe fragment `SafeStep` and proves SN for it via the triple-lex measure.
- **`OperatorKO7/Meta/ComputableMeasure.lean`**: a fully computable termination certificate for `SafeStep`.
- **`OperatorKO7/Meta/Normalize_Safe.lean`**: certified normalizer for `SafeStep` (total + sound; noncomputable by design).
- **`OperatorKO7/Meta/Newman_Safe.lean`**: Newman engine used to derive confluence for the safe fragment under local-join assumptions.
- **`OperatorKO7/Meta/Confluence_Safe.lean`**: local-join / critical-peak lemmas for the safe fragment; also includes an explicit full-kernel caveat showing the overlap at `eqW` creates a non-joinable peak.
- **`OperatorKO7/Meta/SafeStep_Ctx.lean`**: context-closure utilities for safe steps (used by join proofs).
- **`OperatorKO7/Meta/Impossibility_Lemmas.lean`**: impossibility lemmas supporting the conjecture narrative (failure witnesses for simpler measures).
- **`OperatorKO7/Meta/Operational_Incompleteness.lean`**: the "P1–P3 probes" / operational incompleteness scaffolding (namespace `OperatorKO7.OpIncomp`).
- **`OperatorKO7/Meta/ContractProbes.lean`**: small auxiliary probes referenced by the impossibility story.
- **`OperatorKO7/Meta/DM_MPO_Orientation.lean`**: helper lemmas for DM/MPO orientations used in the measures.
- **`OperatorKO7/Meta/CNFOrdinal.lean`**: ordinal/CNF support (used by ordinal-based parts of the development).
- **`OperatorKO7/Meta/GoodsteinCore.lean`**: small, independent Goodstein-style toy core (exposition/witness support).
- **`OperatorKO7/Meta/HydraCore.lean`**: small, independent Hydra-style toy core (exposition/witness support).
- **`OperatorKO7/Meta/FailureModes.lean`**: negative tests / counterexample sketches documenting why naive reasoning fails (kept in the main tree as part of the theory story).
- **`OperatorKO7/Meta/ComputableMeasure_Test.lean`**: small Lean checks that the computable measure API is present (smoke tests).
- **`OperatorKO7/Meta/ComputableMeasure_Verification.lean`**: extra verification lemmas/examples for the computable measure (non-essential but kept for reproducibility).

### Lean tests (`OperatorKO7/Test/`)
- **`OperatorKO7/Test/Sanity.lean`**: minimal test file imported by the build to ensure the package compiles in CI and on fresh machines.

## Citation

If you use this work in your research, please cite both the paper and the software artifact:

### Paper Citation

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
  doi          = {10.48550/arXiv.2512.00081},
  note         = {Submitted for journal publication}
}
```

### Software Artifact Citation

```bibtex
@software{rahnama2024operatorko7_software,
  author       = {Rahnama, Moses},
  title        = {{OperatorKO7: Mechanically-Verified Termination 
                   Proof for a Relational Operator TRS}},
  year         = {2024},
  publisher    = {GitHub},
  url          = {https://github.com/MosesRahnama/OperatorKO7},
  howpublished = {\url{https://github.com/MosesRahnama/OperatorKO7}},
  note         = {Lean 4 formalization accompanying arXiv:2512.00081}
}
```

### Combined Citation (for papers requiring single entry)

```bibtex
@misc{rahnama2024operatorko7_complete,
  author       = {Rahnama, Moses},
  title        = {{Strong Normalization for the Safe Fragment of a Minimal 
                   Rewrite System (Paper + Lean Formalization)}},
  year         = {2024},
  url          = {https://arxiv.org/abs/2512.00081},
  doi          = {10.48550/arXiv.2512.00081},
  note         = {Paper: arXiv:2512.00081; Code: \url{https://github.com/MosesRahnama/OperatorKO7}}
}
```

Alternatively, use the "Cite this repository" feature in the GitHub sidebar, which uses the `CITATION.cff` file.

## Licensing

- **Lean code**: Apache-2.0 (see `LICENSE` at repo root).
- **Paper text**: CC BY-NC-ND 4.0 (see `Paper/LICENSE`).

For commercial permissions (paper or alternative terms), contact: `moses@minaanalytics.com`
