# Artifact Reproducibility

This note is the review-facing reproducibility summary for the active `OperatorKO7`
artifact.

## Exact Pins

- Lean toolchain: `leanprover/lean4:v4.22.0-rc4`
  Source: `lean-toolchain`
- Pinned `mathlib4` commit: `632465e4b02cb70a5dfa4cfe15468e8a62c2bd85`
  Sources: `lakefile.lean`, `lake-manifest.json`
- Full dependency lockfile:
  `lake-manifest.json`

These values should be treated as part of the artifact narrative. The project uses
Mathlib automation heavily enough that replay against a different toolchain or
`mathlib` revision may change proof-checking behavior.

## Minimal Replay

From the repository root:

```bash
lake update
lake exe cache get
lake build
lake exe verifyTpdbExport
```

What this covers:

- `lake build`
  checks the Lean library and executable targets in the active package.
- `lake exe verifyTpdbExport`
  checks the Lean-side TPDB exporter text against both the embedded checked literal
  and the on-disk `Artifacts/ttt2/KO7_full_step.trs` artifact.

Optional documentation refresh:

```bash
python generate_docs.py
```

This regenerates `OperatorKO7_Complete_Documentation.md`, the public file-level map
bundled by the referee snapshot script.

## External Validation Trail

The archived external tool trail lives in `Artifacts/ttt2/` and includes:

- `KO7_full_step.trs`
- TTT2 text outputs
- CPF certificates
- CeTA certification log
- `Artifacts/ttt2/README.md`

This trail is archived and bundled for review. It is not claimed as a Lean theorem
layer; it is an external validation layer attached to the main formal artifact.
The Lean file `Meta/TTT2_CertificateReplay.lean` is only a narrow replay of the
FAST certificate core under Lean definitions, not a CPF parser or a general CeTA
reimplementation.

## Referee Bundle

Generate a reviewer-facing snapshot with:

```bash
python scripts/make_referee_bundle.py
```

Default output:

- `Artifacts/referee-bundles/<timestamped bundle dir>`
- `Artifacts/referee-bundles/<timestamped bundle zip>`

These paths are generated on demand and are not part of the committed repository tree.

The bundle contains:

- exact toolchain/dependency metadata
- Lean sources and build files
- generated file-level documentation
- `VerifyTpdbExport.lean`
- the archived `Artifacts/ttt2/` trail
- the current reproducibility notes
- a generated replay note and machine-readable manifest
- if the sibling private paper tree is available locally, the current manuscript source and PDF

Use `--output-dir` if you want the generated bundle outside the repository tree.

## CI

The repository CI definition is:

- `.github/workflows/build.yml`

That workflow currently provides the baseline package build path. The referee-bundle
script is complementary: it packages the material reviewers need to inspect and replay.

## Micro-Benchmarks

Replay-cost notes for the active artifact state are recorded in:

- `Artifacts/MICRO_BENCHMARKS.md`

That file reports local Lean replay timings together with the archived TTT2 run times
already stored in `Artifacts/ttt2/`.
