import OperatorKO7.Meta.DependencyPairs_TPDBExtraction

/-!
# Generic First-Order Dependency-Pair Extraction

This module abstracts the concrete TPDB-side extraction layer to a generic finite
first-order TRS presentation with arbitrary symbol and variable types. From a finite rule
list it computes:

- the defined heads (left-hand side root symbols),
- the defined call-heads appearing in right-hand sides, and
- the corresponding array-backed extracted call graph.

The TPDB-specific extractor can then be seen as one frontend into this generic layer,
instead of being the theorem shape itself.
-/

namespace OperatorKO7.DependencyPairsFragment

/-- Generic first-order term syntax with variables and function symbols. -/
inductive FOTerm (σ ν : Type) : Type
| var : ν → FOTerm σ ν
| app : σ → List (FOTerm σ ν) → FOTerm σ ν

/-- Generic first-order rewrite rule. -/
structure FORule (σ ν : Type) where
  lhs : FOTerm σ ν
  rhs : FOTerm σ ν

namespace FOTerm

variable {σ ν : Type}

/-- Root head symbol of a first-order term, when present. -/
def head? : FOTerm σ ν → Option σ
| .var _ => none
| .app f _ => some f

/-- All function heads appearing anywhere in a first-order term. -/
def allHeads [DecidableEq σ] : FOTerm σ ν → Finset σ
| .var _ => ∅
| .app f args =>
    insert f <| args.foldl (fun acc t => acc ∪ allHeads t) ∅

end FOTerm

namespace FORule

variable {σ ν : Type}

/-- Root head symbol of the left-hand side of a first-order rule, when present. -/
def lhsHead? (r : FORule σ ν) : Option σ :=
  FOTerm.head? r.lhs

end FORule

/-- Extracted dependency-pair node data for a first-order rule. -/
structure ExtractedFORuleNode (σ ν : Type) [DecidableEq σ] where
  rule : FORule σ ν
  nodeKey : σ
  succKeys : Finset σ

/-- Defined heads of a finite first-order TRS: the function symbols appearing at rule
roots. -/
def foDefinedHeads {σ ν : Type} [DecidableEq σ] (rules : Array (FORule σ ν)) : Finset σ :=
  rules.foldl
    (fun acc r =>
      match FORule.lhsHead? r with
      | some f => insert f acc
      | none => acc)
    ∅

/-- Extract one dependency-pair call-graph node from a first-order rule. -/
def extractFORuleNode? {σ ν : Type} [DecidableEq σ]
    (defined : Finset σ) (r : FORule σ ν) : Option (ExtractedFORuleNode σ ν) :=
  match FORule.lhsHead? r with
  | none => none
  | some f =>
      some
        { rule := r
          nodeKey := f
          succKeys := (FOTerm.allHeads r.rhs).filter (· ∈ defined) }

/-- Extracted dependency-pair call-graph nodes for a finite first-order TRS. -/
def extractFORuleNodes {σ ν : Type} [DecidableEq σ]
    (rules : Array (FORule σ ν)) : Array (ExtractedFORuleNode σ ν) :=
  let defined := foDefinedHeads rules
  rules.filterMap (extractFORuleNode? defined)

/-- Array-backed extracted call graph induced by a finite first-order TRS. -/
def foExtractedCallGraph {σ ν : Type} [DecidableEq σ]
    (rules : Array (FORule σ ν)) : FiniteExtractedCallGraph σ :=
  FiniteExtractedCallGraph.ofArrayMap
    (nodes := extractFORuleNodes rules)
    (nodeKey := ExtractedFORuleNode.nodeKey)
    (succKeys := ExtractedFORuleNode.succKeys)

namespace TPDBBridge

open OperatorKO7

/-- Convert a TPDB term to the generic first-order syntax. -/
def term : TpdbTerm → FOTerm String String
| .var x => .var x
| .app f args => .app f (args.map term)

/-- Convert a TPDB rule to the generic first-order syntax. -/
def rule (r : TpdbRule) : FORule String String where
  lhs := term r.lhs
  rhs := term r.rhs

@[simp] theorem term_head?_eq (t : TpdbTerm) :
    FOTerm.head? (term t) = OperatorKO7.DependencyPairsFragment.TpdbTerm.head? t := by
  cases t <;> simp [term, FOTerm.head?, OperatorKO7.DependencyPairsFragment.TpdbTerm.head?]

@[simp] theorem rule_lhsHead?_eq (r : TpdbRule) :
    FORule.lhsHead? (rule r) = OperatorKO7.DependencyPairsFragment.TpdbRule.lhsHead? r := by
  simp [FORule.lhsHead?, rule, OperatorKO7.DependencyPairsFragment.TpdbRule.lhsHead?, term_head?_eq]

end TPDBBridge

namespace KO7FirstOrder

open OperatorKO7

/-- Generic first-order variable shorthands for the KO7 full-step TRS. -/
def x : FOTerm String String := .var "x"
def y : FOTerm String String := .var "y"
def z : FOTerm String String := .var "z"

/-- Generic first-order constructor / function shorthands for KO7. -/
def void : FOTerm String String := .app "void" []
def delta (t : FOTerm String String) : FOTerm String String := .app "delta" [t]
def integrate (t : FOTerm String String) : FOTerm String String := .app "integrate" [t]
def merge (a b : FOTerm String String) : FOTerm String String := .app "merge" [a, b]
def app (a b : FOTerm String String) : FOTerm String String := .app "app" [a, b]
def recD (b s n : FOTerm String String) : FOTerm String String := .app "recD" [b, s, n]
def eqW (a b : FOTerm String String) : FOTerm String String := .app "eqW" [a, b]

/-- The KO7 full-step TRS as a generic first-order rule list. -/
def ko7FullStepFORules : Array (FORule String String) :=
  #[ ⟨integrate (delta x), void⟩
   , ⟨merge void x, x⟩
   , ⟨merge x void, x⟩
   , ⟨merge x x, x⟩
   , ⟨recD x y void, x⟩
   , ⟨recD x y (delta z), app y (recD x y z)⟩
   , ⟨eqW x x, void⟩
   , ⟨eqW x y, integrate (merge x y)⟩ ]

/-- Concrete extracted nodes for the generic first-order KO7 rule list. -/
def ko7FullStepExtractedNodes : Array (ExtractedFORuleNode String String) :=
  extractFORuleNodes ko7FullStepFORules

/-- Concrete extracted call graph for the generic first-order KO7 rule list. -/
def ko7FullStepExtractedCallGraph : FiniteExtractedCallGraph String :=
  foExtractedCallGraph ko7FullStepFORules

theorem ko7_full_step_extracted_node_count :
    ko7FullStepExtractedNodes.size = 8 := by
  native_decide

theorem ko7_full_step_defined_heads :
    foDefinedHeads ko7FullStepFORules =
      ({ "integrate", "merge", "recD", "eqW" } : Finset String) := by
  native_decide

theorem ko7_full_step_has_recD_successor :
    ∃ n ∈ ko7FullStepExtractedNodes.toList,
      n.nodeKey = "recD" ∧ n.succKeys = ({ "recD" } : Finset String) := by
  native_decide

end KO7FirstOrder

end OperatorKO7.DependencyPairsFragment
