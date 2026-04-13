import OperatorKO7.Meta.ConfessionMethod
import OperatorKO7.Meta.ConfessionMethod_DP

/-!
# Confession Method Instance: Argument Filtering

Argument filtering (Arts-Giesl 2000, within the DP framework) maps each
function symbol to a subset or projection of its argument list. For the
step-duplicating schema:

- π(recur) = 3   (project to the counter argument only)
- π(wrap) = ε    (collapse to nothing)
- π(succ) = 1    (keep the single argument)
- π(base) = ε    (collapse to nothing)

After filtering, the duplicating rule `recur(b, s, succ(n)) → wrap(s, recur(b, s, n))`
becomes `succ(n) → n` in the filtered universe: the wrapper and the duplicated
payload are entirely absent. Termination of the filtered problem is trivial.

Argument filtering is a **structural drop**: it removes arguments from the
proof obligation rather than constructing a new comparison object. The
soundness is licensed by the argument-filtering soundness theorem within
the DP framework, which guarantees that termination of the filtered problem
implies termination of the original system under the conditions of the
framework.

On the step-duplicating schema, argument filtering produces the same
concrete rank as DP + subterm criterion and counter-projection. What differs
is the extraction mechanism (filtering map rather than DP pair extraction or
direct argument selection) and the specific soundness theorem invoked.
-/

namespace OperatorKO7.ConfessionMethodFamily

open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility

/-- Argument filtering as a confession method on KO7.
    Same projection rank; the license is the argument-filtering soundness
    theorem within the DP framework. -/
def argumentFilteringConfession : ConfessionMethod ko7Schema where
  toProjectionRank := dpProjectionRank
  license := SoundnessLicense.argumentFilteringSoundness

/-- On the step-duplicating schema, argument filtering and DP produce
    the same rank function. -/
theorem argumentFiltering_eq_dp_rank :
    argumentFilteringConfession.rank = dpConfession.rank := rfl

end OperatorKO7.ConfessionMethodFamily
