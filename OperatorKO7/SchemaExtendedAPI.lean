import OperatorKO7.PrimitiveSchemaAPI

-- Broader reusable barrier and tooling layer
import OperatorKO7.Meta.QuadraticBarrier
import OperatorKO7.Meta.QuadraticCrossTermBarrier
import OperatorKO7.Meta.MultilinearBarrier
import OperatorKO7.Meta.PolynomialBarrierGeneral
import OperatorKO7.Meta.WPO_PolynomialBarrier
import OperatorKO7.Meta.MaxBarrier
import OperatorKO7.Meta.ArcticBarrier
import OperatorKO7.Meta.TropicalBarrier
import OperatorKO7.Meta.DepthBarrier
import OperatorKO7.Meta.AffineThresholdSharpness
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
import OperatorKO7.Meta.SymbolicComparatorBarrier
import OperatorKO7.Meta.KBO_Impossible
import OperatorKO7.Meta.PumpedBarrierClasses
import OperatorKO7.Meta.StandardPumpLemmas
import OperatorKO7.Meta.BarrierWitness
import OperatorKO7.Meta.BarrierWitness_Extended
import OperatorKO7.Meta.BarrierWitness_Budgets
import OperatorKO7.Meta.SynthesisOracle
import OperatorKO7.Meta.BarrierClass_Classifier
import OperatorKO7.Meta.MutualDuplication_General
import OperatorKO7.Meta.MutualDuplication_CycleFlow
import OperatorKO7.Meta.MutualDuplication_KNode
import OperatorKO7.Meta.MutualDuplication_KNode_Abstract
import OperatorKO7.Meta.MutualDuplication_GraphCycle
import OperatorKO7.Meta.MutualDuplication_Transparent
import OperatorKO7.Meta.MutualDuplication_RelationalGraph
import OperatorKO7.Meta.MutualDuplication_CallGraph
import OperatorKO7.Meta.MutualDuplication_ExtractedCallGraph
import OperatorKO7.Meta.MutualDuplication_PayloadFlow
import OperatorKO7.Meta.MutualDuplication_Preserving
import OperatorKO7.Meta.MutualDuplication_Preserving_KNode
import OperatorKO7.Meta.MutualDuplication_Preserving_Abstract
import OperatorKO7.Meta.MutualDuplication_Preserving_Transparent
import OperatorKO7.Meta.MutualDuplication_PacketGraph
import OperatorKO7.Meta.EscapeTrichotomy_Schema

/-!
# Schema Extended API

Reusable public root above `PrimitiveSchemaAPI`.

This file adds the broader barrier library, executable tooling, and reusable
SCC-level schema extensions. It is intentionally broader than the primitive
root and may expose named-instance corollaries from mixed files under the
current project layout, but it still excludes the KO7-facing bridge and
cross-paper confession-family packaging.

It also exposes the extracted schema half of the escape-trichotomy development
via `Meta/EscapeTrichotomy_Schema.lean`.
-/
