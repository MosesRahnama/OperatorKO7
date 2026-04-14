import OperatorKO7.Meta.MetaHalt_PaperInterface

open OperatorKO7.WitnessOrder
open OperatorKO7.MetaHalt.Signatures
open OperatorKO7.MetaHalt.Predicate

-- Example 1: empty admissibility table, empty loop patterns, no visited
-- catalog -> metaHalt returns `none` (continue searching).
#eval metaHalt
  { goalTags := [], witnessOrderLowerBound := WLevel.transformedCall }
  { level := WLevel.directWhole, features := [], name := "test" }
  SearchTraceSignature.empty
  { rules := [], default := true }
  { patterns := [] }
  100 10

-- Example 2: admissibility table blocks directWhole -> structural block.
#eval metaHalt
  { goalTags := [GoalTag.containsDuplicatingStep],
    witnessOrderLowerBound := WLevel.transformedCall }
  { level := WLevel.directWhole, features := [], name := "additive" }
  SearchTraceSignature.empty
  { rules := [
      { requiredGoalTags := [GoalTag.containsDuplicatingStep],
        requiredFeatures := [], verdict := false } ],
    default := true }
  { patterns := [] }
  100 10

-- Example 3: three loop-pattern observations with threshold 3 -> certified cycle.
#eval metaHalt
  { goalTags := [], witnessOrderLowerBound := WLevel.transformedCall }
  { level := WLevel.importedWhole, features := [], name := "test2" }
  { stepsConsumed := 5, candidateCount := 1,
    traceTags := [TraceTag.loopPatternObserved, TraceTag.loopPatternObserved,
      TraceTag.loopPatternObserved] }
  { rules := [], default := true }
  { patterns := [
      { patternTags := [TraceTag.loopPatternObserved], threshold := 3 } ] }
  100 10
