import OperatorKO7.SchemaAPI
import OperatorKO7.Kernel
import OperatorKO7.Meta.ComputableMeasure
import OperatorKO7.Meta.ComputableMeasure_Verification
import OperatorKO7.Meta.DM_OrderType
import OperatorKO7.Meta.DM_OrderType_LowerBound
import OperatorKO7.Meta.Mu3c_Image_LowerBound
import OperatorKO7.Meta.RecCore
import OperatorKO7.Meta.QuadraticBarrier
import OperatorKO7.Meta.QuadraticCrossTermBarrier
import OperatorKO7.Meta.AffineThresholdSharpness
import OperatorKO7.Meta.ObjectAxiom_Ablation
import OperatorKO7.Meta.MutualDuplication_Case
import OperatorKO7.Meta.MutualDuplication_General
import OperatorKO7.Meta.MutualDuplication_Preserving
import OperatorKO7.Meta.MutualDuplication_Transparent
import OperatorKO7.Meta.MatrixBarrier2
import OperatorKO7.Meta.MatrixBarrierD
import OperatorKO7.Meta.MatrixBarrierLex
import OperatorKO7.Meta.MatrixBarrierMix2
import OperatorKO7.Meta.MatrixBarrierFunctional
import OperatorKO7.Meta.MatrixProjectionCoverage
import OperatorKO7.Meta.MultilinearBarrier
import OperatorKO7.Meta.PolynomialBarrierGeneral
import OperatorKO7.Meta.MaxBarrier
import OperatorKO7.Meta.ArcticBarrier
import OperatorKO7.Meta.SymbolicComparatorBarrier
import OperatorKO7.Meta.KBO_Impossible
import OperatorKO7.Meta.ScalarProjectionBarrier
import OperatorKO7.Meta.BarrierClass_Classifier
import OperatorKO7.Meta.SynthesisOracle
import OperatorKO7.Meta.PumpedBarrierClasses
import OperatorKO7.Meta.StandardPumpLemmas
import OperatorKO7.Meta.EscapeTrichotomy
import OperatorKO7.Meta.DepthBarrier
import OperatorKO7.Meta.PrecedenceBarrier
import OperatorKO7.Meta.TypedBarrierSurvival
import OperatorKO7.Meta.ManySortedBarrierSurvival
import OperatorKO7.Meta.TextbookDupInstance
import OperatorKO7.Meta.TPDB_Export
import OperatorKO7.Meta.DependencyPairs_Fragment
import OperatorKO7.Meta.DependencyPairs_Works
import OperatorKO7.Meta.DP_BaseOrder_Boundary
import OperatorKO7.Meta.ContextClosed_SN
import OperatorKO7.Meta.NormalizeSafe_LowerBound
import OperatorKO7.Meta.EqW_Guard_Barrier
import OperatorKO7.Meta.ContextClosed_SN_Full
import OperatorKO7.Meta.ContextClosedBarrier
import OperatorKO7.Meta.SafeStep_Complexity
import OperatorKO7.Meta.SafeStep_Complexity_Ordinal
import OperatorKO7.Meta.SafeStep_Complexity_FastGrowing
import OperatorKO7.Meta.SafeStep_Complexity_MW_Ctx
import OperatorKO7.Meta.SafeStep_Complexity_MW_CtxExact
import OperatorKO7.Meta.SafeStepCtx_Complexity_Exponential
import OperatorKO7.Meta.SafeRoot_Complexity
import OperatorKO7.Meta.SafeStepCtx_Confluence
import OperatorKO7.Meta.EqGuardedConfluence
import OperatorKO7.Meta.Reachability_Complexity
import OperatorKO7.Meta.MPO_FullStep
import OperatorKO7.Meta.MPO_Precedence_Barrier
import OperatorKO7.Meta.MPO_ProofTheoreticBound
import OperatorKO7.Meta.PolyInterpretation_FullStep
import OperatorKO7.Meta.TTT2_CertificateReplay
import OperatorKO7.Meta.TropicalBarrier
import OperatorKO7.Meta.SharingBarrierLift

/-!
Public entrypoint for the `OperatorKO7` Lean library.

Why this file exists:
- Acts as the minimal import surface for downstream users and reviewers.
- Keeps the default build stable by importing the core kernel and the canonical computable SafeStep development.
- Includes the computable-measure verification suite in the default build path.
- Includes ordinal calibration upper-bound lemmas (`DM_OrderType`) in the default build path.
- Includes Phase-B lower-bound scaffolding (`DM_OrderType_LowerBound`) in the default build path.
- Additional modules (normalizer, confluence) are imported directly where needed
  (e.g. in `OperatorKO7/Meta/Examples_Publish.lean`).
-/
