# OperatorKO7

This README is a repository map with a short set of entry points.
It stays file-descriptive and does not restate theorem or benchmark claims.

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

## Reproducibility Pins

- Lean toolchain: `leanprover/lean4:v4.22.0-rc4`
- Pinned `mathlib4` commit: `632465e4b02cb70a5dfa4cfe15468e8a62c2bd85`
- Full transitive dependency lockfile: `lake-manifest.json`

These pins are part of the artifact story, not just build metadata. The project uses
Mathlib automation heavily enough that the exact Lean toolchain and `mathlib` revision
should be treated as review-facing inputs.

## Artifact Replay

Minimal local replay:

```bash
lake update
lake exe cache get
lake build
lake exe verifyTpdbExport
```

Referee-bundle and TPDB-prep support:

```bash
python scripts/make_referee_bundle.py
python scripts/stage_tpdb_submission.py
```

Artifact-facing docs:
- `artifact/REPRODUCIBILITY.md`:
  exact toolchain pins, local replay path, and referee-bundle generation.
- `artifact/TPDB_SUBMISSION_PREP.md`:
  staged prep notes for a future TPDB submission; not the submission itself.
- `Artifacts/ttt2/README.md`:
  archived TTT2/CeTA trail and source files already stored in the repository.
- `.github/workflows/build.yml`:
  repository CI build path.

## Recommended Entry Points

- `OperatorKO7/SchemaAPI.lean`:
  single-import public API for the reusable schema-level barrier theory, separate from KO7-specific certification and artifact plumbing.
- `OperatorKO7/Kernel.lean`:
  start here for the core syntax and root rewrite relation.
- `OperatorKO7/Meta/StepDuplicatingSchema.lean`:
  generic direct-measure impossibility framework.
- `OperatorKO7/Meta/Newman_Safe.lean`:
  guarded-fragment confluence, normalization, and reachability.
- `OperatorKO7/Meta/ContextClosed_SN_Full.lean`:
  full unguarded context-closed strong normalization in Lean.
- `OperatorKO7/Meta/PolyInterpretation_FullStep.lean` and `OperatorKO7/Meta/MPO_FullStep.lean`:
  the two internal full root-step orientation proofs.
- `OperatorKO7_Complete_Documentation.md`:
  full generated file-by-file map.

## Top-Level Layout

- `OperatorKO7.lean`: library entrypoint imports.
- `OperatorKO7/`: Lean source tree.
- `Artifacts/`: external tool artifacts.
- `artifact/`: artifact-facing reproducibility notes and generated bundle staging area.
- `Archive/`: archived or superseded working material.
- `.github/`: workflow and repository metadata.
- `scripts/`: small helper scripts for referee-bundle generation and TPDB-prep staging.
- `scripts/make_referee_bundle.py`:
  builds a review-facing source/artifact bundle, including generated docs and the
  archived external validation trail; if the sibling private paper tree is present,
  it also bundles the current manuscript source and PDF under `paper/`.
- `scripts/stage_tpdb_submission.py`:
  stages a local TPDB-prep directory from the archived KO7 `.trs` artifact and
  writes metadata/provenance templates; it does not perform the upstream submission.
- `VerifyTpdbExport.lean`: runnable TPDB exporter/file verifier.
- `generate_docs.py`: documentation-generation script.
- `OperatorKO7_Complete_Documentation.md`: extended file-level map.
- `Docs/KO7_BLUEPRINT.md` and `Docs/ko7_blueprint.json`: proof-dependency map from paper labels to Lean declarations and back.

## Lean Source Layout

### Top-Level Lean and Build Files

- `lakefile.lean`:
  Lake package configuration; declares the `OperatorKO7` library root and the `verifyTpdbExport` executable target.
- `OperatorKO7.lean`:
  public library import surface; collects the canonical modules built by `lake build OperatorKO7`.
- `OperatorKO7/SchemaAPI.lean`:
  stable public API surface for downstream users who want only the reusable schema-level barrier theory and executable boundary tooling.
- `VerifyTpdbExport.lean`:
  executable root for `lake exe verifyTpdbExport`; checks the embedded TPDB text against the on-disk `.trs` artifact.

### Core

- `OperatorKO7/Kernel.lean`:
  core term syntax (`Trace`), kernel root relation (`Step`), and closures (`StepStar`).

### Meta Modules

#### Safe fragment and certification

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
- `OperatorKO7/Meta/ContextClosed_SN_Full.lean`:
  full unguarded context-closed SN via the polynomial witness.
- `OperatorKO7/Meta/ContextClosedBarrier.lean`:
  root-to-context corollaries lifting the direct barrier stack to `StepCtxFull`.
- `OperatorKO7/Meta/Confluence_Safe.lean`:
  local-join lemmas; `localJoin_all_safe`.
- `OperatorKO7/Meta/Newman_Safe.lean`:
  Newman instantiation; `confluentSafe`, unique normal forms, reachability decidability.
- `OperatorKO7/Meta/SafeStepCtx_Confluence.lean`:
  unconditional confluence for `SafeStepCtx`, together with the exact Newman obstruction equivalence and the discharged global contextual local-join theorem.
- `OperatorKO7/Meta/EqGuardedConfluence.lean`:
  intermediate root fragment keeping the full rule set except the bad `eqW` diff overlap on reflexive inputs; proves root confluence for that wider fragment.
- `OperatorKO7/Meta/NormalizeSafe_LowerBound.lean`:
  exact-cost lower-bound family for the certified normalizer.
- `OperatorKO7/Meta/SafeStep_Complexity.lean`:
  contextual derivation-length bounds for the guarded fragment.
- `OperatorKO7/Meta/SafeStep_Complexity_Ordinal.lean`:
  size-indexed tower-exponential derivation-length bound for `SafeStepCtx` via `ctxFuel`.
- `OperatorKO7/Meta/SafeStep_Complexity_FastGrowing.lean`:
  explicit fast-growing-hierarchy-style envelope for the same `SafeStepCtx` derivation-length bound, majorizing the `towerBound` estimate by a size-indexed finite-level `fastGrow` family.
- `OperatorKO7/Meta/OrdinalHierarchy.lean`:
  generic `slowGrowing` and `cichon` hierarchies on Mathlib ordinal notations below `ε₀`.
- `OperatorKO7/Meta/SafeStep_Complexity_MW_Root.lean`:
  notation bridge from the calibrated `μ3c` ordinal to `ONote` / `NONote`, plus the root Cichon bound `safeStepPow_length_le_mwRootBound`.
- `OperatorKO7/Meta/SafeStep_Complexity_MW_Ctx.lean`:
  conservative context-closed Moser-Weiermann lift `mwCtxNote` / `mwCtxBound`, with `safeStepCtx_length_le_mwCtxBound`, the `ω^ω·2` calibration lemma `mwCtxNote_lt_opow_omega_mul_two`, and explicit obstruction theorems showing the root-side calibrated note does not directly descend along all `SafeStepCtx` steps.
- `OperatorKO7/Meta/SafeRoot_Complexity.lean`:
  exact-length root-normalizer realizations and upper envelopes via `ctxFuel` / `complexity_bound` and `normalizeSafeSteps_le_mwRootBound`.
- `OperatorKO7/Meta/Reachability_Complexity.lean`:
  explicit certified cost envelope for guarded reachability-to-safe-normal-form decisions, plus a linear lower-bound family.
- `OperatorKO7/Meta/EqW_Guard_Barrier.lean`:
  full-step `eqW` overlap obstruction and guard-necessity results.

#### Barrier stack and direct-measure impossibility

- `OperatorKO7/Meta/StepDuplicatingSchema.lean`:
  parametric four-role schema; generic additive / transparent-compositional / affine barriers.
- `OperatorKO7/Meta/BarrierWitness.lean`:
  constructive counterexample extractors (`BarrierCertificate`-style witnesses).
- `OperatorKO7/Meta/BarrierWitness_Extended.lean`:
  extended witness extractors for restricted quadratic, max-plus, and projected
  matrix-side families, with bundled failure certificates.
- `OperatorKO7/Meta/Impossibility_Lemmas.lean`:
  machine-checked failed-measure catalog.
- `OperatorKO7/Meta/Conjecture_Boundary.lean`:
  no-go theorems, `GlobalOrients` framework.
- `OperatorKO7/Meta/CompositionalMeasure_Impossibility.lean`:
  impossibility theorems (Tier 1 and Tier 2), DP escape clause, `GlobalOrients` bridge.
- `OperatorKO7/Meta/QuadraticBarrier.lean`:
  restricted degree-2 barrier without step-counter coupling.
- `OperatorKO7/Meta/QuadraticCrossTermBarrier.lean`:
  bounded step-counter cross-term barrier.
- `OperatorKO7/Meta/MultilinearBarrier.lean`:
  bounded multilinear barrier with frozen-coefficient dominance at base.
- `OperatorKO7/Meta/PolynomialBarrierGeneral.lean`:
  generalized bounded polynomial barrier with repeated variables and a base-dominance failure condition.
- `OperatorKO7/Meta/MaxBarrier.lean`:
  schema-level max-plus constructor-local barrier.
- `OperatorKO7/Meta/ArcticBarrier.lean`:
  arctic-style primary-projection corollary of the max barrier for tool-facing direct interpretations.
- `OperatorKO7/Meta/TropicalBarrier.lean`:
  broader tropical primary-projection barrier lifting the max-style obstruction to finite primary projections with a strict natural shadow.
- `OperatorKO7/Meta/PumpedBarrierClasses.lean`:
  strengthened pumped subclasses for affine, quadratic, generalized bounded-polynomial, multilinear, max-plus, and projection-based conditional barriers.
- `OperatorKO7/Meta/StandardPumpLemmas.lean`:
  reusable successor-/wrapper-growth lemmas and subclass constructors.
- `OperatorKO7/Meta/AffineThresholdSharpness.lean`:
  canonical affine sharpness family for the generic affine contradiction bound.
- `OperatorKO7/Meta/DepthBarrier.lean`:
  KO7-specific max-depth family and corresponding barrier.
- `OperatorKO7/Meta/PrecedenceBarrier.lean`:
  KO7-specific pure head-precedence family and corresponding barrier.
- `OperatorKO7/Meta/TypedBarrierSurvival.lean`:
  simply-typed first-order recursor fragment; typed additive and affine barrier-survival results.

#### Matrix, SCC, and escape extensions

- `OperatorKO7/Meta/RecCore.lean`:
  RecΔ-core (4 constructors); impossibility restated on minimal sub-signature.
- `OperatorKO7/Meta/MatrixBarrier2.lean`:
  tracked dimension-2 componentwise barrier and symmetric second-component lemmas.
- `OperatorKO7/Meta/MatrixBarrierD.lean`:
  tracked fixed-dimension componentwise barrier.
- `OperatorKO7/Meta/MatrixBarrierLex.lean`:
  tracked dimension-2 lexicographic barrier.
- `OperatorKO7/Meta/MatrixBarrierMix2.lean`:
  balanced mixed-coordinate dimension-2 barrier via aggregate-sum projection.
- `OperatorKO7/Meta/MatrixBarrierFunctional.lean`:
  weighted scalar-projection componentwise barrier unifying tracked-coordinate and aggregate-sum projection arguments.
- `OperatorKO7/Meta/MatrixProjectionCoverage.lean`:
  explicit fixed-row and row-sum corollaries making the matrix-side projection coverage visible for tool-facing discussion.
- `OperatorKO7/Meta/ScalarProjectionBarrier.lean`:
  scalar-projection lift theorem rederiving blocked vector and pair families from scalar barriers.
- `OperatorKO7/Meta/MutualDuplication_Case.lean`:
  concrete alternating worked instance.
- `OperatorKO7/Meta/MutualDuplication_General.lean`:
  bounded two-node SCC composite-duplication theorems.
- `OperatorKO7/Meta/MutualDuplication_Preserving.lean`:
  multiplicity-preserving synchronized SCC barrier.
- `OperatorKO7/Meta/MutualDuplication_Transparent.lean`:
  transparent-compositional and projected matrix-style extensions of the bounded two-node SCC barrier.
- `OperatorKO7/Meta/EscapeTrichotomy.lean`:
  explicit direct-universe escape trichotomy, now including the generalized bounded-polynomial family, plus the projection-based extension for weighted functional and balanced mixed-coordinate matrix families.
- `OperatorKO7/Meta/SymbolicComparatorBarrier.lean`:
  symbolic variable-condition barrier for direct duplication-sensitive comparators.
- `OperatorKO7/Meta/KBO_Impossible.lean`:
  explicit KO7 KBO-style impossibility corollary extracted from the symbolic barrier.

#### Dependency pairs, ordinal calibration, and full-step orienters

- `OperatorKO7/Meta/DependencyPairs_Fragment.lean`:
  reusable narrow DP layer (`DPProjection`, `SCCCycle`).
- `OperatorKO7/Meta/DependencyPairs_Works.lean`:
  extracted DP pair for `rec_succ`; projection decrease and DP-chain well-foundedness (`wf_DPPairRev`).
- `OperatorKO7/Meta/DP_BaseOrder_Boundary.lean`:
  boundary result showing the extracted DP pair already admits a simple linear polynomial-style base order.
- `OperatorKO7/Meta/DM_OrderType.lean`:
  DM-to-ordinal embedding; ε₀ bridge; per-step strictness; upper-bound calibration.
- `OperatorKO7/Meta/DM_OrderType_LowerBound.lean`:
  `CNFωω` canonical carrier; surjectivity below ω^ω, reflection, rank bridge, and exact DM-component order-type calibration.
- `OperatorKO7/Meta/MPO_FullStep.lean`:
  KO7-specialized MPO orientation and well-foundedness on the full root relation.
- `OperatorKO7/Meta/MPO_Precedence_Barrier.lean`:
  explicit bad-precedence obstruction for the KO7 MPO shape.
- `OperatorKO7/Meta/MPO_ProofTheoreticBound.lean`:
  explicit ordinal envelope for the fixed-signature KO7 MPO ranking, below `Ordinal.veblen 7 0`.
- `OperatorKO7/Meta/PolyInterpretation_FullStep.lean`:
  nonlinear polynomial orientation and well-foundedness on the full root relation.
- `OperatorKO7/Meta/LinearRec_Ablation.lean`:
  linear recursor variant; `simpleSize` orientation (ablation).
- `OperatorKO7/Meta/ObjectAxiom_Ablation.lean`:
  directed wrapper-collapse surrogate and preserved direct barriers.

#### Artifact and tooling support

- `OperatorKO7/Meta/BarrierClass_Classifier.lean`:
  coefficient-table classifier for the formalized barrier families.
- `OperatorKO7/Meta/SynthesisOracle.lean`:
  small certified oracle layer around the basic and extended barrier witnesses.
- `OperatorKO7/Meta/TPDB_Export.lean`:
  Lean-side TPDB export for the full KO7 root TRS.
- `OperatorKO7/Meta/TTT2_CertificateReplay.lean`:
  narrow Lean-side replay of the mathematical core of the FAST DP/subterm certificate.
- `OperatorKO7/Meta/SharingBarrierLift.lean`:
  sharing-aware surrogate showing the tree-style direct barrier can fail once payload sharing is admitted.

### Tests

- `OperatorKO7/Test/Sanity.lean`:
  basic compilation/evaluation checks.
- `OperatorKO7/Test/TPDB_Export.lean`:
  smoke tests for TPDB export text generation and related verifier-facing declarations.

## Artifact Folders

- `Artifacts/ttt2/`:
  TRS input, CPF outputs, and certification logs.

## Notes

- `lake build` checks the full artifact; `lake build OperatorKO7` checks the library only.
- `lake exe verifyTpdbExport` checks the Lean exporter against both the embedded text literal and the on-disk `Artifacts/ttt2/KO7_full_step.trs` file.
- `python scripts/make_referee_bundle.py` assembles a reviewer-facing snapshot with a manifest, replay note, and archived external validation trail.
- `OperatorKO7_Complete_Documentation.md` is the large generated file-by-file reference if you need more than this repository map.
