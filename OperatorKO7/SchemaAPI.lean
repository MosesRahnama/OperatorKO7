-- Core schema and barrier theorems
import OperatorKO7.Meta.StepDuplicatingSchema
import OperatorKO7.Meta.FreeStepDuplicatingSyntax
import OperatorKO7.Meta.FreeStepDuplicatingTraceBridge

-- Nonlinear scalar barrier extensions
import OperatorKO7.Meta.QuadraticBarrier
import OperatorKO7.Meta.QuadraticCrossTermBarrier
import OperatorKO7.Meta.MultilinearBarrier
import OperatorKO7.Meta.PolynomialBarrierGeneral
import OperatorKO7.Meta.WPO_PolynomialBarrier
import OperatorKO7.Meta.MaxBarrier
import OperatorKO7.Meta.ArcticBarrier
import OperatorKO7.Meta.TropicalBarrier

-- Max-aggregative depth barrier (schema + KO7)
import OperatorKO7.Meta.DepthBarrier

-- Affine-bound sharpness
import OperatorKO7.Meta.AffineThresholdSharpness

-- Vector / matrix-side barriers
import OperatorKO7.Meta.MatrixBarrier2
import OperatorKO7.Meta.MatrixBarrierD
import OperatorKO7.Meta.MatrixBarrierLex
import OperatorKO7.Meta.MatrixBarrierLexD
import OperatorKO7.Meta.MatrixBarrierLexPermD
import OperatorKO7.Meta.MatrixBarrierMix2
import OperatorKO7.Meta.MatrixBarrierFunctional
import OperatorKO7.Meta.ScalarProjectionBarrier
import OperatorKO7.Meta.ProjectedPrimaryBarrier
import OperatorKO7.Meta.MatrixProjectionCoverage

-- Symbolic comparator barriers
import OperatorKO7.Meta.SymbolicComparatorBarrier
import OperatorKO7.Meta.KBO_Impossible

-- Strengthened subclasses and pump infrastructure
import OperatorKO7.Meta.PumpedBarrierClasses
import OperatorKO7.Meta.StandardPumpLemmas

-- Second named schema instance
import OperatorKO7.Meta.TextbookDupInstance

-- Executable boundary tooling
import OperatorKO7.Meta.BarrierWitness
import OperatorKO7.Meta.BarrierWitness_Extended
import OperatorKO7.Meta.BarrierWitness_Budgets
import OperatorKO7.Meta.SynthesisOracle
import OperatorKO7.Meta.BarrierClass_Classifier

-- Confession method family (escape side)
import OperatorKO7.Meta.ConfessionMethod
import OperatorKO7.Meta.ConfessionMethod_RouteEvidence
import OperatorKO7.Meta.ConfessionMethod_Family

-- Reusable DP fragment (schema-level rank / SCC descent)
import OperatorKO7.Meta.DependencyPairs_Fragment

-- Graph / finite-SCC extraction utilities
import OperatorKO7.Meta.GraphPathExtraction
import OperatorKO7.Meta.FiniteGraphReachability
import OperatorKO7.Meta.FiniteGraphSCC

-- Delayed-duplication SCC barrier family (Thm. "alternating-cycle composite-step barrier")
import OperatorKO7.Meta.MutualDuplication_General
import OperatorKO7.Meta.MutualDuplication_CycleFlow
import OperatorKO7.Meta.MutualDuplication_KNode
import OperatorKO7.Meta.MutualDuplication_KNode_Abstract
import OperatorKO7.Meta.MutualDuplication_GraphCycle
import OperatorKO7.Meta.MutualDuplication_Transparent
import OperatorKO7.Meta.MutualDuplication_RelationalGraph
import OperatorKO7.Meta.MutualDuplication_CallGraph
import OperatorKO7.Meta.MutualDuplication_ExtractedCallGraph

-- Multiplicity-preserving synchronized-SCC barrier family (Thm. "preserving-scc")
import OperatorKO7.Meta.MutualDuplication_PayloadFlow
import OperatorKO7.Meta.MutualDuplication_Preserving
import OperatorKO7.Meta.MutualDuplication_Preserving_KNode
import OperatorKO7.Meta.MutualDuplication_Preserving_Abstract
import OperatorKO7.Meta.MutualDuplication_Preserving_Transparent
import OperatorKO7.Meta.MutualDuplication_PacketGraph
import OperatorKO7.Meta.EscapeTrichotomy_Schema

-- Cross-paper-capable schema interfaces
import OperatorKO7.Meta.BenchmarkedPrimitiveRecursionFamily
import OperatorKO7.Meta.OperationalIncompleteness

-- Paper 2 (Failure Floor) schema-level quantitative / structural layer
import OperatorKO7.Meta.SchemaCanonicalTrace
import OperatorKO7.Meta.SchemaConfessionDominance
import OperatorKO7.Meta.SchemaOffsetAndWrapper
import OperatorKO7.Meta.SchemaNormMismatch
import OperatorKO7.Meta.SchemaSeedCarrierFactorization
import OperatorKO7.Meta.SchemaForgettingWitness
import OperatorKO7.Meta.SchemaOperationalIncompleteness
import OperatorKO7.Meta.SchemaWitnessOrder

/-!
# Public Schema API: Hybrid Convenience Root

This module is the **hybrid convenience root** for the step-duplicating
development. It remains available as the broad one-import surface, but it is no
longer the only public entry point.

The split public roots are now:

- `OperatorKO7.PrimitiveSchemaAPI`: conservative primitive/schema-parametric core
- `OperatorKO7.SchemaExtendedAPI`: broader reusable barrier/tooling/SCC layer
- `OperatorKO7.CrossPaperAPI`: KO7-facing bridge and cross-paper layer

`SchemaAPI` continues to re-export the wider convenience surface for existing
downstream users. Because it still bundles confession-family and cross-paper
packaging, it should not be treated as the strict primitive boundary.

What this module provides:

Core schema definition:
- `StepDuplicatingSchema`: the four-role schema (base/succ/wrap/recur)
- `StepDuplicatingSystem`: schema + a step relation containing the dup rule
- `GlobalOrients`: the property that a measure globally orients a relation
- free generated schema `freeSchema` and its public uniqueness theorems
- true image shadow `PrimitiveTraceImage` inside `Trace`, together with the
  free-to-KO7 bridge on the primitive fragment

Barrier theorems (schema-level):
- Additive and transparent-compositional impossibility
- Affine / linear constructor-local barrier, together with a canonical affine
  sharpness family showing the generic pump bound is exact
- Restricted quadratic, bounded cross-term quadratic, bounded multilinear, and
  generalized degree-bounded polynomial barriers
- WPO-facing polynomial-branch corollary built on the bounded polynomial barrier
- Max-plus barrier, arctic primary-projection corollary, and tropical
  primary-projection continuation
- Schema-level max-aggregative depth barrier (`MaxDepthMeasure`)
- Fixed-dimension tracked componentwise vector barrier
- Dimension-2 lexicographic pair barrier
- Arbitrary finite tracked-primary lexicographic vector barrier
- Permutation-priority finite tracked-primary lexicographic vector barrier
- Balanced mixed-coordinate dimension-2 barrier
- Weighted scalar-projection componentwise barrier
- Scalar-projection meta-theorem
- Projected-primary dominance meta-theorem subsuming the tracked componentwise
  and tracked-primary lexicographic vector barriers
- Explicit fixed-row and row-sum matrix-projection coverage corollaries
- Symbolic variable-condition barrier (KBO-style) and KBO corollary

SCC-level barrier extensions:
- Delayed-duplication: alternating two-node SCC, abstract one-cycle metatheorem,
  finite cyclic `k+1`-node generalization, raw-graph cycle formulations,
  transparent-compositional and projection corollaries, relation-level,
  call-graph, and array-backed extracted-call-graph construction layers.
- Multiplicity-preserving synchronized SCC: abstract payload-flow metatheorems,
  finite synchronized-packet generalization, packet-transparent and
  projection corollaries, and raw-graph packet formulations.
- Graph-side utilities: path extraction from transitive-closure proofs,
  finite decidable reachability, and finite-SCC search packaging.
- Extracted schema half of the escape-trichotomy development.

Strengthened subclasses and pump infrastructure:
- Pumped subclasses with internalized growth conditions
- Reusable successor-pump and wrap-pump lemmas

Executable boundary tooling:
- Computable barrier-witness extractors (`additive_witness`, etc.)
- Extended witness extractors for quadratic, max-plus, and projected matrix families
- Canonical witness-budget theorems for the current extractor layer
- Synthesis-oracle interface
- Decidable coefficient-table classifier

Named schema instances:
- KO7 (via the imports under `OperatorKO7.CompositionalImpossibility`, threaded
  through the barrier files).
- Textbook duplicating rule `f(x, s(y)) → g(x, f(x, y))` with direct additive,
  transparent-compositional, and affine corollaries and specialized witness
  aliases.

Confession-method family (escape side):
- Dependency pairs + subterm criterion
- Direct counter-projection alias
- Size-change termination (SCT)
- Argument filtering
- Shared `RouteEvidence` adapter layer above the four concrete route records
- Family-level API for rank agreement, certified forgetting, and license tags
- Reusable DP fragment (schema-level rank / SCC-path descent)

Cross-paper-capable schema interfaces:
- Six-member primitive-recursion family classification over the `RecCore` signature
- `CertifiedForgettingWitness` / `PayloadOperationalIncompleteness` schema
  packaging

What this module does NOT provide:

KO7-specific results (kernel definitions, KO7-only ablations, the certified
`SafeStep` / `SafeStepCtx` / `StepCtxFull` certification chain, confluence
and normalizer, ordinal calibration, MPO/polynomial full-step proofs, TTT2
/ CeTA validation, the explicit KO7 escape trichotomy, `EqW_Guard_Barrier`,
`PrecedenceBarrier` — which depends on `merge_cancel`, a KO7-specific
non-duplicating rule — and the `SafeStep`-based complexity bounds) live in
the main `OperatorKO7` import path. This module is for users who want
the broad convenience surface rather than one of the stricter split roots.

Usage:

```lean
import OperatorKO7.SchemaAPI

-- Define your own schema instance and apply any barrier theorem directly.
```
-/
