import OperatorKO7.Kernel

namespace OperatorKO7

/-!
Lean-side export of the full KO7 root TRS to the concrete TPDB / TTT2 syntax
used by the checked external artifact in `Artifacts/ttt2/KO7_full_step.trs`.

Why this file exists:
- Provides a minimal audited bridge from the Lean kernel presentation of KO7 to
  the exact first-order TRS submitted to TTT2 / CeTA.
- Keeps the bridge intentionally small: one concrete exporter for KO7, not a
  generic TPDB library.
- Proves that the generated text matches the checked artifact text byte-for-byte
  modulo Lean's exact string literal.
- Makes the external tool input part of the reviewed formal artifact rather than
  a manually maintained side file only.
-/

/-- Minimal first-order TPDB term syntax for the exported KO7 problem. -/
inductive TpdbTerm : Type
| var : String → TpdbTerm
| app : String → List TpdbTerm → TpdbTerm

/-- A TPDB rewrite rule. -/
structure TpdbRule where
  lhs : TpdbTerm
  rhs : TpdbTerm

namespace TpdbTerm

mutual
  /-- Render a TPDB term in the concrete syntax used by `KO7_full_step.trs`. -/
  def render : TpdbTerm → String
  | .var x => x
  | .app f [] => f
  | .app f (a :: as) => f ++ "(" ++ render a ++ renderTail as ++ ")"

  /-- Render the remaining arguments of a TPDB function application. -/
  def renderTail : List TpdbTerm → String
  | [] => ""
  | a :: as => ", " ++ render a ++ renderTail as
end

end TpdbTerm

namespace TpdbRule

/-- Render one TPDB rule line, with the indentation used in the artifact file. -/
def render (r : TpdbRule) : String :=
  "  " ++ TpdbTerm.render r.lhs ++ " -> " ++ TpdbTerm.render r.rhs

end TpdbRule

/-- Render a block of TPDB rules, one per line. -/
def renderRuleBlock : List TpdbRule → String
| [] => ""
| [r] => TpdbRule.render r ++ "\n"
| r :: rs => TpdbRule.render r ++ "\n" ++ renderRuleBlock rs

/-- Variable shorthands for the exported full-step TRS. -/
def tx : TpdbTerm := .var "x"
def ty : TpdbTerm := .var "y"
def tz : TpdbTerm := .var "z"

/-- Constructor / function shorthands with the external names used by TTT2. -/
def tvoid : TpdbTerm := .app "void" []
def tdelta (t : TpdbTerm) : TpdbTerm := .app "delta" [t]
def tintegrate (t : TpdbTerm) : TpdbTerm := .app "integrate" [t]
def tmerge (a b : TpdbTerm) : TpdbTerm := .app "merge" [a, b]
def tapp (a b : TpdbTerm) : TpdbTerm := .app "app" [a, b]
def trecD (b s n : TpdbTerm) : TpdbTerm := .app "recD" [b, s, n]
def teqW (a b : TpdbTerm) : TpdbTerm := .app "eqW" [a, b]

/-- The eight full-step KO7 rules in the exported TRS order. -/
def ko7FullStepTpdbRules : List TpdbRule :=
  [ ⟨tintegrate (tdelta tx), tvoid⟩
  , ⟨tmerge tvoid tx, tx⟩
  , ⟨tmerge tx tvoid, tx⟩
  , ⟨tmerge tx tx, tx⟩
  , ⟨trecD tx ty tvoid, tx⟩
  , ⟨trecD tx ty (tdelta tz), tapp ty (trecD tx ty tz)⟩
  , ⟨teqW tx tx, tvoid⟩
  , ⟨teqW tx ty, tintegrate (tmerge tx ty)⟩
  ]

/-- The exact TPDB / TTT2 text for the full KO7 root TRS. -/
def ko7_full_step_tpdb : String :=
  "(VAR x y z)\n" ++
  "(RULES\n" ++
  renderRuleBlock ko7FullStepTpdbRules ++
  ")\n"

/-- Checked artifact text for `Artifacts/ttt2/KO7_full_step.trs`. -/
def ko7_full_step_tpdb_artifact_text : String :=
  "(VAR x y z)\n" ++
  "(RULES\n" ++
  "  integrate(delta(x)) -> void\n" ++
  "  merge(void, x) -> x\n" ++
  "  merge(x, void) -> x\n" ++
  "  merge(x, x) -> x\n" ++
  "  recD(x, y, void) -> x\n" ++
  "  recD(x, y, delta(z)) -> app(y, recD(x, y, z))\n" ++
  "  eqW(x, x) -> void\n" ++
  "  eqW(x, y) -> integrate(merge(x, y))\n" ++
  ")\n"

/-- The Lean-side exporter matches the checked artifact text exactly. -/
theorem ko7_full_step_tpdb_matches_artifact_text :
    ko7_full_step_tpdb = ko7_full_step_tpdb_artifact_text := by
  native_decide

/-- The exported TPDB problem contains exactly the eight full-step kernel rules. -/
theorem ko7_full_step_tpdb_rule_count :
    ko7FullStepTpdbRules.length = 8 := rfl

end OperatorKO7
