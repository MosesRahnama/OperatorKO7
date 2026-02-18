import OperatorKO7.Kernel
import OperatorKO7.Meta.ComputableMeasure

/-!
Public entrypoint for the `OperatorKO7` Lean library.

Why this file exists:
- Acts as the minimal import surface for downstream users and reviewers.
- Keeps the default build stable by importing the core kernel and the canonical computable SafeStep development.
- Additional modules (normalizer, confluence) are imported directly where needed
  (e.g. in `OperatorKO7/Meta/Examples_Publish.lean`).
-/
