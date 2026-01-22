import OperatorKO7.Kernel
import OperatorKO7.Meta.Termination_KO7

/-!
Public entrypoint for the `OperatorKO7` Lean library.

Why this file exists:
- Acts as the minimal import surface for downstream users and reviewers.
- Keeps the default build stable by importing only the core kernel and the main SafeStep development.
- Additional modules (normalizer, confluence, computable measure) are imported directly where needed
  (e.g. in `OperatorKO7/Meta/Examples_Publish.lean`).
-/
