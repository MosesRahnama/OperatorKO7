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

## Recommended Entry Points

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
- `Archive/`: archived or superseded working material.
- `.github/`: workflow and repository metadata.
- `VerifyTpdbExport.lean`: runnable TPDB exporter/file verifier.
- `generate_docs.py`: documentation-generation script.
- `OperatorKO7_Complete_Documentation.md`: extended file-level map.

## Lean Source Layout

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
- `OperatorKO7/Meta/Confluence_Safe.lean`:
  local-join lemmas; `localJoin_all_safe`.
- `OperatorKO7/Meta/Newman_Safe.lean`:
  Newman instantiation; `confluentSafe`, unique normal forms, reachability decidability.
- `OperatorKO7/Meta/NormalizeSafe_LowerBound.lean`:
  exact-cost lower-bound family for the certified normalizer.
- `OperatorKO7/Meta/SafeStep_Complexity.lean`:
  contextual derivation-length bounds for the guarded fragment.
- `OperatorKO7/Meta/EqW_Guard_Barrier.lean`:
  full-step `eqW` overlap obstruction and guard-necessity results.

#### Barrier stack and direct-measure impossibility

- `OperatorKO7/Meta/StepDuplicatingSchema.lean`:
  parametric four-role schema; generic additive / transparent-compositional / affine barriers.
- `OperatorKO7/Meta/BarrierWitness.lean`:
  constructive counterexample extractors (`BarrierCertificate`-style witnesses).
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
- `OperatorKO7/Meta/MaxBarrier.lean`:
  schema-level max-plus constructor-local barrier.
- `OperatorKO7/Meta/PumpedBarrierClasses.lean`:
  strengthened pumped subclasses for conditional barriers.
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
- `OperatorKO7/Meta/ScalarProjectionBarrier.lean`:
  scalar-projection lift theorem rederiving blocked vector and pair families from scalar barriers.
- `OperatorKO7/Meta/MutualDuplication_Case.lean`:
  concrete alternating worked instance.
- `OperatorKO7/Meta/MutualDuplication_General.lean`:
  bounded two-node SCC composite-duplication theorems.
- `OperatorKO7/Meta/MutualDuplication_Preserving.lean`:
  multiplicity-preserving synchronized SCC barrier.
- `OperatorKO7/Meta/EscapeTrichotomy.lean`:
  explicit direct-universe escape trichotomy.
- `OperatorKO7/Meta/SymbolicComparatorBarrier.lean`:
  symbolic variable-condition barrier for direct duplication-sensitive comparators.

#### Dependency pairs, ordinal calibration, and full-step orienters

- `OperatorKO7/Meta/DependencyPairs_Fragment.lean`:
  reusable narrow DP layer (`DPProjection`, `SCCCycle`).
- `OperatorKO7/Meta/DependencyPairs_Works.lean`:
  extracted DP pair for `rec_succ`; projection decrease and DP-chain well-foundedness (`wf_DPPairRev`).
- `OperatorKO7/Meta/DM_OrderType.lean`:
  DM-to-ordinal embedding; ε₀ bridge; per-step strictness; upper-bound calibration.
- `OperatorKO7/Meta/DM_OrderType_LowerBound.lean`:
  `CNFωω` canonical carrier; surjectivity below ω^ω, reflection, rank bridge.
- `OperatorKO7/Meta/MPO_FullStep.lean`:
  KO7-specialized MPO orientation and well-foundedness on the full root relation.
- `OperatorKO7/Meta/MPO_Precedence_Barrier.lean`:
  explicit bad-precedence obstruction for the KO7 MPO shape.
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
  small certified oracle layer around barrier witnesses.
- `OperatorKO7/Meta/TPDB_Export.lean`:
  Lean-side TPDB export for the full KO7 root TRS.

### Tests

- `OperatorKO7/Test/Sanity.lean`:
  basic compilation/evaluation checks.

## Artifact Folders

- `Artifacts/ttt2/`:
  TRS input, CPF outputs, and certification logs.

## Notes

- `VerifyTpdbExport.lean` plus `lake exe verifyTpdbExport` check that the Lean-side TPDB export matches the checked on-disk `.trs` artifact.
- `lake build` checks the full artifact; `lake build OperatorKO7` checks the library only.
- `OperatorKO7_Complete_Documentation.md` is the large generated file-by-file reference if you need more than this repository map.
