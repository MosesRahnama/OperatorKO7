import OperatorKO7.Meta.ConfessionMethod_Unification

/-!
# Confession-Method Route Evidence

This module is the shared boundary for the generic `RouteEvidence` layer above
the four concrete KO7 confession-method entry routes.

It packages the route-local evidence story in one import:

- the four concrete route witnesses,
- their generic `RouteEvidence` adapters,
- the generic forgetting-witness lift,
- the KO7-local unification theorems showing that all four routes factor
  through one common generic route-evidence object.

The underlying definitions still live where they belong:

- the abstract `RouteEvidence` interface in `StepDuplicatingSchema.lean`,
- the method-specific witness records in the four route files,
- the convergence results in `ConfessionMethod_Unification.lean`.

This file exists to give that distributed layer a single import boundary for
downstream users and for the later public API split.
-/

namespace OperatorKO7.ConfessionMethodFamily

/- No additional declarations. This module is an import boundary only. -/

end OperatorKO7.ConfessionMethodFamily
