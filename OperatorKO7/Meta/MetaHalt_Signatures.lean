import OperatorKO7.Meta.WitnessOrder
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Count
import Mathlib.Data.Nat.Basic

/-!
# META-HALT Signatures

This module defines the finite decidable signatures consumed by the
META-HALT supervisory predicate.

The design principle is finiteness by construction. Every structure here
carries `DecidableEq`, and the tables (admissibility, certified loop
patterns) carry finite decidable lookup operations.

Key identifiers:

- `LanguageSignature` : finite tag plus feature record for a witness language;
- `ObligationSignature` : finite feature record for an obligation;
- `SearchTraceSignature` : finite record of object-level search observations;
- `AdmissibilityRule`, `AdmissibilityTable` : pre-declared admissibility
  contract;
- `LoopPattern`, `LoopPatternTable` : certified loop-pattern family;
- `FeatureTag`, `GoalTag`, `TraceTag` : enumerated finite tag types consumed
  by the signature records.
-/

namespace OperatorKO7.MetaHalt.Signatures

open OperatorKO7
open OperatorKO7.WitnessOrder

/-- Finite set of witness-language feature tags. Each constructor corresponds
    to a structural property of a proof language that is consumed by the
    admissibility contract in Definition 5.10. -/
inductive FeatureTag
  | admitsCrossVariableCoupling
  | admitsSymbolPrecedence
  | admitsPolynomialInterpretation
  | admitsMaxPlusAlgebra
  | admitsMatrixInterpretation
  | isProjectionBased
  | isSizeChangeBased
  | requiresExternalSoundnessLicense
  | importsWellFoundedRelation
  | admitsContextClosure
  deriving DecidableEq, Repr

/-- Finite set of obligation feature tags. Each constructor records a
    structural property of the obligation (goal) that drives admissibility
    classification. The duplication tag is the load-bearing one for the
    operational-incompleteness paper. -/
inductive GoalTag
  | containsDuplicatingStep
  | isFirstOrderFinitary
  | isConstructorTRS
  | hasWrapperContext
  | hasBaseGroundingRule
  | hasCounterDescentArgument
  | admitsCallGraphExtraction
  deriving DecidableEq, Repr

/-- Finite set of trace-signature tags. Each constructor records a structural
    observation about the object-level search trace that is consumed by
    META-HALT clauses (ii) and (iii) of Definition 5.3. -/
inductive TraceTag
  | candidateEmitted
  | candidateRejectedByChecker
  | budgetExhausted
  | loopPatternObserved
  | structuralBlockDetected
  deriving DecidableEq, Repr

/-- Sanity check that `DecidableEq` is available on all three tag types. -/
example : DecidableEq FeatureTag := inferInstance
example : DecidableEq GoalTag := inferInstance
example : DecidableEq TraceTag := inferInstance

/-- Finite signature of a witness language.

    `level` locates the language in the four-level hierarchy of
    `WitnessOrder.lean`. `features` is the finite set of structural
    properties the language admits. `name` is a human-readable tag retained
    only for audit reports; supervisory decisions are computed from `level`
    and `features` alone. -/
structure LanguageSignature where
  level : WLevel
  features : List FeatureTag
  name : String := ""
  deriving DecidableEq, Repr

/-- Does the language carry a given feature? -/
def LanguageSignature.hasFeature (L : LanguageSignature) (t : FeatureTag) : Bool :=
  decide (t ∈ L.features)

/-- Finite signature of an obligation.

    `goalTags` is the set of structural properties that characterize the
    obligation. `witnessOrderLowerBound` records the minimum witness order the
    admissibility contract requires for this obligation. -/
structure ObligationSignature where
  goalTags : List GoalTag
  witnessOrderLowerBound : WLevel
  deriving DecidableEq, Repr

/-- Does the obligation carry a given structural goal tag? -/
def ObligationSignature.hasTag (O : ObligationSignature) (t : GoalTag) : Bool :=
  decide (t ∈ O.goalTags)

/-- Finite signature of the current object-level search trace inside one
    witness language.

    `stepsConsumed` is the object-level search budget already spent.
    `traceTags` is the list of observations the supervisory layer has
    received. `candidateCount` is the number of candidate witnesses the
    language has emitted so far. -/
structure SearchTraceSignature where
  stepsConsumed : Nat
  candidateCount : Nat
  traceTags : List TraceTag
  deriving DecidableEq, Repr

/-- Has the trace observed a given event tag? -/
def SearchTraceSignature.observed (T : SearchTraceSignature) (t : TraceTag) : Bool :=
  decide (t ∈ T.traceTags)

/-- The empty trace used at the entry point of any language. -/
def SearchTraceSignature.empty : SearchTraceSignature :=
  { stepsConsumed := 0, candidateCount := 0, traceTags := [] }

/-- One row of the admissibility table.

    Represents a pre-declared rule of the form:
    "if the obligation has all tags in `requiredGoalTags` and the language
    has all features in `requiredFeatures`, then the language is marked
    `admissible := verdict`." -/
structure AdmissibilityRule where
  requiredGoalTags : List GoalTag
  requiredFeatures : List FeatureTag
  verdict : Bool
  note : String := ""
  deriving DecidableEq, Repr

/-- A table of admissibility rules applied in declaration order.

    The first rule whose left-hand side matches determines the verdict. If
    no rule matches, the default verdict is returned. -/
structure AdmissibilityTable where
  rules : List AdmissibilityRule
  default : Bool
  deriving Repr

/-- Does an admissibility rule match a given obligation/language pair? -/
def AdmissibilityRule.matches (r : AdmissibilityRule)
    (O : ObligationSignature) (L : LanguageSignature) : Bool :=
  r.requiredGoalTags.all (fun t => O.hasTag t) &&
    r.requiredFeatures.all (fun f => L.hasFeature f)

/-- Evaluate the admissibility table in declaration order. -/
def AdmissibilityTable.admits
    (tbl : AdmissibilityTable) (O : ObligationSignature) (L : LanguageSignature) : Bool :=
  match tbl.rules.find? (fun r => r.matches O L) with
  | some r => r.verdict
  | none => tbl.default

instance (tbl : AdmissibilityTable) (O : ObligationSignature)
    (L : LanguageSignature) : Decidable (tbl.admits O L = true) :=
  inferInstance

/-- One entry of the certified loop-pattern family of Definition 5.11. -/
structure LoopPattern where
  patternTags : List TraceTag
  threshold : Nat
  name : String := ""
  deriving DecidableEq, Repr

/-- Certified loop-pattern family. -/
structure LoopPatternTable where
  patterns : List LoopPattern
  deriving Repr

/-- Count the occurrences of `t` in the trace-tag list. -/
def SearchTraceSignature.countTag (T : SearchTraceSignature) (t : TraceTag) : Nat :=
  T.traceTags.count t

/-- Does a loop pattern fire on the current search trace? -/
def LoopPattern.fires (p : LoopPattern) (T : SearchTraceSignature) : Bool :=
  p.patternTags.all (fun t => p.threshold ≤ T.countTag t)

/-- Does any certified loop pattern fire on the current search trace? -/
def LoopPatternTable.anyFires (tbl : LoopPatternTable) (T : SearchTraceSignature) : Bool :=
  tbl.patterns.any (fun p => p.fires T)

/-- A finite catalog entry: one language at a budget. -/
structure CatalogEntry where
  language : LanguageSignature
  budget : Nat
  deriving DecidableEq, Repr

/-- Finite witness-language catalog used by the supervisory loop. -/
structure Catalog where
  entries : List CatalogEntry
  deriving Repr

/-- Cardinality of the catalog. -/
def Catalog.size (C : Catalog) : Nat :=
  C.entries.length

/-- Look up the catalog entry for a language, if present. -/
def Catalog.entryOf (C : Catalog) (L : LanguageSignature) : Option CatalogEntry :=
  C.entries.find? (fun e => e.language = L)

/-- `DecidableEq` on language signatures is available from `deriving`. -/
def languageSignature_decEq : DecidableEq LanguageSignature := inferInstance

/-- `DecidableEq` on obligation signatures is available from `deriving`. -/
def obligationSignature_decEq : DecidableEq ObligationSignature := inferInstance

/-- `DecidableEq` on search-trace signatures is available from `deriving`. -/
def searchTraceSignature_decEq : DecidableEq SearchTraceSignature := inferInstance

/-- `DecidableEq` on catalog entries is available from `deriving`. -/
def catalogEntry_decEq : DecidableEq CatalogEntry := inferInstance

end OperatorKO7.MetaHalt.Signatures
