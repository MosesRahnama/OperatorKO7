import OperatorKO7.Meta.DependencyPairs_FiniteCarrierView

/-!
# KO7 Kernel Rules as a Generic First-Order TRS

This module packages the KO7 full root-step rules directly as a finite first-order TRS over
an internal symbol type, rather than through the external TPDB string syntax. It shows
that the generic first-order dependency-pair extraction layer can be driven from an
artifact-internal presentation as well.
-/

namespace OperatorKO7.DependencyPairsFragment.KernelFirstOrder

/-- Internal first-order symbol type for the KO7 full-step TRS. -/
inductive Symbol
| void
| delta
| integrate
| merge
| app
| recD
| eqW
deriving DecidableEq, Repr

abbrev Term := OperatorKO7.DependencyPairsFragment.FOTerm Symbol String
abbrev Rule := OperatorKO7.DependencyPairsFragment.FORule Symbol String

/-- Variable shorthands for the internal KO7 first-order presentation. -/
def x : Term := .var "x"
def y : Term := .var "y"
def z : Term := .var "z"

/-- Internal symbol constructor shorthands. -/
def void : Term := .app Symbol.void []
def delta (t : Term) : Term := .app Symbol.delta [t]
def integrate (t : Term) : Term := .app Symbol.integrate [t]
def merge (a b : Term) : Term := .app Symbol.merge [a, b]
def app (a b : Term) : Term := .app Symbol.app [a, b]
def recD (b s n : Term) : Term := .app Symbol.recD [b, s, n]
def eqW (a b : Term) : Term := .app Symbol.eqW [a, b]

/-- KO7 full-step rules as an internal first-order TRS. -/
def ko7FullStepRules : Array Rule :=
  #[ ⟨integrate (delta x), void⟩
   , ⟨merge void x, x⟩
   , ⟨merge x void, x⟩
   , ⟨merge x x, x⟩
   , ⟨recD x y void, x⟩
   , ⟨recD x y (delta z), app y (recD x y z)⟩
   , ⟨eqW x x, void⟩
   , ⟨eqW x y, integrate (merge x y)⟩ ]

/-- Trivial internal engine carrier for the KO7 full-step TRS. -/
inductive EngineTag
| full
deriving DecidableEq, Repr

/-- Finite rule carrier for the KO7 full-step TRS. -/
inductive RuleId
| integrate_delta
| merge_void_left
| merge_void_right
| merge_idem
| rec_zero
| rec_succ
| eq_refl
| eq_diff
deriving Fintype, DecidableEq, Repr

/-- Left-hand sides indexed by the finite KO7 rule carrier. -/
def ruleLhs : RuleId → Term
| .integrate_delta => integrate (delta x)
| .merge_void_left => merge void x
| .merge_void_right => merge x void
| .merge_idem => merge x x
| .rec_zero => recD x y void
| .rec_succ => recD x y (delta z)
| .eq_refl => eqW x x
| .eq_diff => eqW x y

/-- Right-hand sides indexed by the finite KO7 rule carrier. -/
def ruleRhs : RuleId → Term
| .integrate_delta => void
| .merge_void_left => x
| .merge_void_right => x
| .merge_idem => x
| .rec_zero => x
| .rec_succ => app y (recD x y z)
| .eq_refl => void
| .eq_diff => integrate (merge x y)

instance : OperatorKO7.DependencyPairsFragment.HasFiniteRawFirstOrderView EngineTag Symbol String where
  Rule := Rule
  Term := Term
  termView := OperatorKO7.DependencyPairsFragment.instHasFirstOrderTermViewFOTerm Symbol String
  rules _ := ko7FullStepRules
  lhs := FORule.lhs
  rhs := FORule.rhs

instance : OperatorKO7.DependencyPairsFragment.HasFiniteHeadRuleView EngineTag Symbol :=
  OperatorKO7.DependencyPairsFragment.finiteHeadRuleViewOfRaw EngineTag Symbol String

instance : OperatorKO7.DependencyPairsFragment.HasFiniteCarrierRawFirstOrderView EngineTag Symbol String where
  Rule := RuleId
  ruleFintype := inferInstance
  ruleDecEq := inferInstance
  Term := Term
  termView := OperatorKO7.DependencyPairsFragment.instHasFirstOrderTermViewFOTerm Symbol String
  lhs := ruleLhs
  rhs := ruleRhs

instance : OperatorKO7.DependencyPairsFragment.HasFiniteCarrierHeadView EngineTag Symbol :=
  OperatorKO7.DependencyPairsFragment.finiteCarrierHeadViewOfFiniteCarrierRaw
    EngineTag Symbol String

instance : OperatorKO7.DependencyPairsFragment.HasFiniteCarrierExtractedView EngineTag Symbol :=
  OperatorKO7.DependencyPairsFragment.finiteCarrierExtractedViewOfHeadCarrier
    EngineTag Symbol

/-- KO7 full-step rules packaged through the generic internal-engine view. -/
def ko7Engine : OperatorKO7.DependencyPairsFragment.FiniteFirstOrderEngine Symbol String :=
  OperatorKO7.DependencyPairsFragment.HasFiniteFirstOrderView.toFiniteFirstOrderEngine EngineTag.full

/-- KO7 full-step rules packaged through the finite rule-carrier engine view. -/
noncomputable def ko7CarrierEngine :
    OperatorKO7.DependencyPairsFragment.FiniteCarrierFirstOrderEngine Symbol String :=
  OperatorKO7.DependencyPairsFragment.HasFiniteCarrierFirstOrderView.toFiniteCarrierFirstOrderEngine
    EngineTag.full

/-- KO7 full-step rules recovered directly from the finite rule-carrier first-order surface. -/
noncomputable def ko7CarrierFirstOrderEngine :
    OperatorKO7.DependencyPairsFragment.FiniteFirstOrderEngine Symbol String :=
  OperatorKO7.DependencyPairsFragment.HasFiniteCarrierFirstOrderView.toFiniteFirstOrderEngine
    (ε := EngineTag) (σ := Symbol) (ν := String) EngineTag.full

/-- KO7 full-step rules packaged through the smaller head / call-head interface. -/
def ko7HeadEngine : OperatorKO7.DependencyPairsFragment.FiniteHeadRuleEngine Symbol :=
  OperatorKO7.DependencyPairsFragment.FiniteHeadRuleEngine.ofRawFirstOrderView
    (ε := EngineTag) (σ := Symbol) (ν := String) EngineTag.full

/-- KO7 full-step rules recovered directly from the typeclass-level head-view surface. -/
def ko7HeadViewEngine : OperatorKO7.DependencyPairsFragment.FiniteHeadRuleEngine Symbol :=
  OperatorKO7.DependencyPairsFragment.HasFiniteHeadRuleView.toFiniteHeadRuleEngine EngineTag.full

/-- KO7 full-step rules recovered directly from the finite rule-carrier head-view surface. -/
noncomputable def ko7CarrierHeadEngine : OperatorKO7.DependencyPairsFragment.FiniteHeadRuleEngine Symbol :=
  OperatorKO7.DependencyPairsFragment.HasFiniteCarrierFirstOrderView.toFiniteHeadRuleEngine
    (ε := EngineTag) (σ := Symbol) (ν := String) EngineTag.full

/-- KO7 full-step rules recovered directly from the finite head-carrier surface. -/
noncomputable def ko7CarrierHeadOnlyEngine : OperatorKO7.DependencyPairsFragment.FiniteHeadRuleEngine Symbol :=
  OperatorKO7.DependencyPairsFragment.HasFiniteCarrierHeadView.toFiniteHeadRuleEngine
    (ε := EngineTag) (σ := Symbol) EngineTag.full

/-- KO7 full-step rules recovered directly from the finite extracted-data carrier surface. -/
noncomputable def ko7CarrierExtractedGraph :
    OperatorKO7.DependencyPairsFragment.FiniteExtractedCallGraph Symbol :=
  OperatorKO7.DependencyPairsFragment.HasFiniteCarrierExtractedView.extractedCallGraph
    (ε := EngineTag) (κ := Symbol) EngineTag.full

/-- Extracted nodes for the internal KO7 first-order TRS. -/
def ko7FullStepExtractedNodes :=
  ko7Engine.extractedNodes

/-- Extracted call graph for the internal KO7 first-order TRS. -/
def ko7FullStepExtractedCallGraph :
    OperatorKO7.DependencyPairsFragment.FiniteExtractedCallGraph Symbol :=
  ko7Engine.extractedCallGraph

theorem ko7_full_step_rule_count :
    ko7FullStepRules.size = 8 := by
  native_decide

theorem ko7_carrier_rule_card :
    Fintype.card RuleId = 8 := by
  native_decide

theorem ko7_full_step_extracted_node_count :
    ko7FullStepExtractedNodes.size = 8 := by
  native_decide

theorem ko7_full_step_defined_heads :
    ko7Engine.definedHeads =
      ({ Symbol.integrate, Symbol.merge, Symbol.recD, Symbol.eqW } : Finset Symbol) := by
  native_decide

theorem ko7_head_engine_defined_heads :
    ko7HeadEngine.definedHeads = ko7Engine.definedHeads := by
  native_decide

theorem ko7_head_engine_extracted_node_count :
    ko7HeadEngine.extractedNodes.size = 8 := by
  native_decide

theorem ko7_head_view_engine_matches :
    ko7HeadViewEngine.definedHeads = ko7HeadEngine.definedHeads := by
  native_decide

theorem ko7_full_step_has_recD_successor :
    ∃ n ∈ ko7FullStepExtractedNodes.toList,
      n.nodeKey = Symbol.recD ∧ n.succKeys = ({ Symbol.recD } : Finset Symbol) := by
  native_decide

theorem ko7_head_engine_has_recD_successor :
    ∃ n ∈ ko7HeadEngine.extractedNodes.toList,
      n.nodeKey = Symbol.recD ∧ n.succKeys = ({ Symbol.recD } : Finset Symbol) := by
  native_decide

end OperatorKO7.DependencyPairsFragment.KernelFirstOrder
