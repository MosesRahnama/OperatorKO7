import OperatorKO7.Meta.StepDuplicatingSchema
import OperatorKO7.Meta.FreeStepDuplicatingSyntax
import OperatorKO7.Meta.TextbookDupInstance
import OperatorKO7.Meta.DependencyPairs_Fragment
import OperatorKO7.Meta.GraphPathExtraction
import OperatorKO7.Meta.FiniteGraphReachability
import OperatorKO7.Meta.FiniteGraphSCC
import OperatorKO7.Meta.SchemaCanonicalTrace
import OperatorKO7.Meta.SchemaConfessionDominance
import OperatorKO7.Meta.SchemaOffsetAndWrapper
import OperatorKO7.Meta.SchemaNormMismatch
import OperatorKO7.Meta.SchemaSeedCarrierFactorization
import OperatorKO7.Meta.SchemaForgettingWitness
import OperatorKO7.Meta.SchemaOperationalIncompleteness
import OperatorKO7.Meta.SchemaWitnessOrder
import OperatorKO7.Meta.EscapeTrichotomy_Schema

/-!
# Primitive Schema API

Conservative public root for the *primitive* step-duplicating schema layer.

This file intentionally re-exports only modules whose public content is framed
directly over `StepDuplicatingSchema`, `StepDuplicatingSystem`, the free schema,
or similarly schema-parametric structures. It excludes:

- KO7-facing bridge modules over `Trace`,
- the confession-family convergence stack,
- the cross-paper primitive-recursion packaging,
- and the mixed barrier/tooling layer that still carries named-instance or
  KO7-facing corollaries under the current file layout.

The goal is a small, stable import path for downstream users who want the
schema-parametric core without the broader project-specific surface.
-/
