import OperatorKO7.Meta.ConfessionMethod
import OperatorKO7.Meta.ConfessionMethod_DP

/-!
# Confession Method Instance: Direct Counter-Projection (Subterm Criterion)

The subterm criterion applied directly to argument positions of the defined
symbol F, without passing through the dependency-pair extraction step.

On the two-rule schema:
- Select argument position 3 of F (the counter)
- Check: S(n) ▷ n (strict subterm containment)
- The step argument Y is never evaluated

This is structurally identical to DP on the step-duplicating schema because
the schema has a single defined symbol with a single recursive call site.
On more complex systems with multiple defined symbols or multiple recursive
calls, the two methods diverge: DP extracts marked pair symbols and builds
a dependency graph, while direct counter-projection operates on the original
symbol's argument positions.

The underlying rank is the same `ProjectionRank` as DP. What differs is
the soundness license: the subterm criterion is applied directly to the
rule's argument positions, not to dependency-pair symbols.
-/

namespace OperatorKO7.ConfessionMethodFamily

open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

/-- Counter-projection via direct subterm criterion on argument position 3.
    Same rank as DP on this schema; different soundness license. -/
def counterProjectionConfession : ConfessionMethod ko7Schema where
  toProjectionRank := dpProjectionRank
  license := SoundnessLicense.subtermCriterionDirect

/-- On the step-duplicating schema, counter-projection and DP produce the
    same rank function. This is a theorem, not a coincidence: the schema
    has exactly one recursive call with exactly one strictly decreasing
    argument, so every method that extracts the recursive-call structure
    and finds the descent coordinate will find the same coordinate. -/
theorem counterProjection_eq_dp_rank :
    counterProjectionConfession.rank = dpConfession.rank := rfl

end OperatorKO7.ConfessionMethodFamily
