import OperatorKO7.Kernel
import OperatorKO7.Meta.ComputableMeasure
import OperatorKO7.Meta.ComputableMeasure_Verification
import OperatorKO7.Meta.DM_OrderType
import OperatorKO7.Meta.DM_OrderType_LowerBound
import OperatorKO7.Meta.RecCore
import OperatorKO7.Meta.ContextClosed_SN
import OperatorKO7.Meta.MPO_FullStep

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
