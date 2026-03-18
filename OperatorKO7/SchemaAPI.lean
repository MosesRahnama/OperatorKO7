-- Core schema and barrier theorems
import OperatorKO7.Meta.StepDuplicatingSchema

-- Nonlinear scalar barrier extensions
import OperatorKO7.Meta.QuadraticBarrier
import OperatorKO7.Meta.QuadraticCrossTermBarrier
import OperatorKO7.Meta.MultilinearBarrier
import OperatorKO7.Meta.PolynomialBarrierGeneral
import OperatorKO7.Meta.MaxBarrier
import OperatorKO7.Meta.ArcticBarrier

-- Vector / matrix-side barriers
import OperatorKO7.Meta.MatrixBarrier2
import OperatorKO7.Meta.MatrixBarrierD
import OperatorKO7.Meta.MatrixBarrierLex
import OperatorKO7.Meta.MatrixBarrierMix2
import OperatorKO7.Meta.MatrixBarrierFunctional
import OperatorKO7.Meta.ScalarProjectionBarrier

-- Symbolic comparator barriers
import OperatorKO7.Meta.SymbolicComparatorBarrier
import OperatorKO7.Meta.KBO_Impossible

-- Strengthened subclasses and pump infrastructure
import OperatorKO7.Meta.PumpedBarrierClasses
import OperatorKO7.Meta.StandardPumpLemmas

-- Executable boundary tooling
import OperatorKO7.Meta.BarrierWitness
import OperatorKO7.Meta.BarrierWitness_Extended
import OperatorKO7.Meta.SynthesisOracle
import OperatorKO7.Meta.BarrierClass_Classifier

/-!
# Public Schema API — Reusable Barrier Theory for Step-Duplicating Recursors

This module is the **stable public entry point** for the reusable schema-level
barrier theory. It re-exports the generic impossibility theorems, escape
characterization infrastructure, and executable boundary tooling that apply to
**any** step-duplicating schema, not only to KO7.

## What this module provides

### Core schema definition
- `StepDuplicatingSchema` — the four-role schema (base/succ/wrap/recur)
- `StepDuplicatingSystem` — schema + a step relation containing the dup rule
- `GlobalOrients` — the property that a measure globally orients a relation

### Barrier theorems (schema-level)
- Additive and transparent-compositional impossibility
- Affine / linear constructor-local barrier
- Restricted quadratic, bounded cross-term quadratic barriers
- Bounded multilinear barrier
- Generalized degree-bounded polynomial barrier
- Max-plus barrier and arctic primary-projection corollary
- Fixed-dimension tracked componentwise vector barrier
- Dimension-2 lexicographic pair barrier
- Balanced mixed-coordinate dimension-2 barrier
- Weighted scalar-projection componentwise barrier
- Scalar-projection meta-theorem
- Symbolic variable-condition barrier (KBO-style) and KBO corollary

### Strengthened subclasses and pump infrastructure
- Pumped subclasses with internalized growth conditions
- Reusable successor-pump and wrap-pump lemmas

### Executable boundary tooling
- Computable barrier-witness extractors (`additive_witness`, etc.)
- Extended witness extractors for quadratic, max-plus, and projected matrix families
- Synthesis-oracle interface
- Decidable coefficient-table classifier

## What this module does NOT provide

KO7-specific results (kernel definitions, KO7 instantiations, the certified
normalizer, confluence, ordinal calibration, MPO/polynomial full-step proofs,
TTT2/CeTA validation, SCC theorems, ablations) live in the main
`OperatorKO7` import path. This module is for users who want **only** the
reusable barrier theory for their own step-duplicating systems.

## Usage

```lean
import OperatorKO7.SchemaAPI

-- Define your own schema instance and apply any barrier theorem directly.
```
-/
