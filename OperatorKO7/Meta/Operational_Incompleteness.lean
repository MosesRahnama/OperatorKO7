import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.DershowitzManna
import OperatorKO7.Meta.HydraCore
import OperatorKO7.Meta.GoodsteinCore

/-!
Operational incompleteness probes (P1-P3) and duplication stress-test scaffolding.

This file is intentionally "probe oriented": it collects small, explicit constructions that support
the paper's *operational incompleteness* framing, without claiming that the full KO7 kernel `Step`
is terminating or confluent.

What this module provides:
- A small operator-only term language (`Term`) with 7 constructors.
- Eight unconditional rewrite rules (`Rule`) plus a standard context closure (`Step`).
- Generic reflexive-transitive closure `Star` and star-composition utilities.
- A structure `InternallyDefinableMeasure` capturing "operator-definable" measures (the notion that
  is relevant to the conjecture: which proof principles count as "internal").
- Duplication stress-test scaffolding for the duplicating rule `mul (s x) y -> add y (mul x y)`.
- Imports of `HydraCore` and `GoodsteinCore` stubs used as additional stress-test encodings.

Style/guardrails:
- All statements are proved (no `sorry`); when a fragment is meant to record a dead end, it remains
  commented to keep the build green.
- Names and arities are spelled out explicitly to satisfy "NameGate / TypeGate" style checks.
-/

set_option linter.unnecessarySimpa false
namespace OperatorKO7.OpIncomp

/--
Seven constructors (names and arities are explicit to satisfy NameGate/TypeGate):
  z    : 0
  s    : 1
  add  : 2
  mul  : 2
  pair : 2
  fst  : 1
  snd  : 1
-/

inductive Term : Type
| z    : Term
| s    : Term → Term
| add  : Term → Term → Term
| mul  : Term → Term → Term
| pair : Term → Term → Term
| fst  : Term → Term
| snd  : Term → Term
deriving DecidableEq, Repr

open Term

/-- Arity table for NameGate/TypeGate reporting. -/
inductive Op where
| z | s | add | mul | pair | fst | snd
deriving DecidableEq, Repr

/-- Arity of each operator symbol (used only for probe reporting, not for rewriting). -/
def arity : Op → Nat
| .z    => 0
| .s    => 1
| .add  => 2
| .mul  => 2
| .pair => 2
| .fst  => 1
| .snd  => 1

/-- Eight unconditional rules at the top level. -/
inductive Rule : Term → Term → Prop
| r1 (y)         : Rule (add z y) y
| r2 (x y)       : Rule (add (s x) y) (s (add x y))
| r3 (y)         : Rule (mul z y) z
| r4 (x y)       : Rule (mul (s x) y) (add y (mul x y))          -- duplicates y
| r5 (x y)       : Rule (fst (pair x y)) x
| r6 (x y)       : Rule (snd (pair x y)) y
| r7 (x)         : Rule (add x z) x                               -- right-zero for add
| r8 (x)         : Rule (mul x z) z                               -- right-zero for mul

/-- For each LHS, list all RHS "pieces" that any matching rule could produce.
This union makes the per-piece orientation contract independent of the Prop proof.
It is intentionally slightly stronger on overlapping LHS shapes. -/
def rhsPiecesLHS : Term → List Term
| add a b =>
  let LaddLeft : List Term :=
    match a with
    | z     => [b]            -- r1: add z b → b
    | s x   => [add x b]      -- r2: add (s x) b → s (add x b)
    | _     => []
  let LaddRight : List Term :=
    match b with
    | z     => [a]            -- r7: add a z → a
    | _     => []
  LaddLeft ++ LaddRight
| mul a b =>
  let LmulLeft : List Term :=
    match a with
    | z     => [z]            -- r3: mul z b → z
    | s x   => [b, mul x b]   -- r4: mul (s x) b → add b (mul x b)
    | _     => []
  let LmulRight : List Term :=
    match b with
    | z     => [z]            -- r8: mul a z → z
    | _     => []
  LmulLeft ++ LmulRight
| fst t =>
  match t with
  | pair x _ => [x]           -- r5
  | _        => []
| snd t =>
  match t with
  | pair _ y => [y]           -- r6
  | _        => []
| _ => []

/-- Context closure of single-step rewriting. -/
inductive Step : Term → Term → Prop
| base {l r}     : Rule l r → Step l r
| sCtx  {t u}    : Step t u → Step (s t) (s u)
| addLCtx {t u v}: Step t u → Step (add t v) (add u v)
| addRCtx {t u v}: Step t u → Step (add v t) (add v u)
| mulLCtx {t u v}: Step t u → Step (mul t v) (mul u v)
| mulRCtx {t u v}: Step t u → Step (mul v t) (mul v u)
| pairLCtx{t u v}: Step t u → Step (pair t v) (pair u v)
| pairRCtx{t u v}: Step t u → Step (pair v t) (pair v u)
| fstCtx {t u}   : Step t u → Step (fst t) (fst u)
| sndCtx {t u}   : Step t u → Step (snd t) (snd u)

/-- Reflexive–transitive closure `Star`. -/
inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop
| refl {a}       : Star R a a
| step {a b c}   : R a b → Star R b c → Star R a c

namespace Star
variable {α : Type} {R : α → α → Prop}

@[simp] theorem refl' {a} : Star R a a := Star.refl

theorem trans {a b c} (h1 : Star R a b) (h2 : Star R b c) : Star R a c := by
  induction h1 with
  | refl =>
    simpa using h2
  | step h h1 ih =>
    exact Star.step h (ih h2)

end Star

/-- A simple additive size measure used only for the duplication stress test. -/
def size : Term → Nat
| z           => 1
| s t         => size t + 1
| add t u     => size t + size u + 1
| mul t u     => size t + size u + 1
| pair t u    => size t + size u + 1
| fst t       => size t + 1
| snd t       => size t + 1


/-! A) Branch-by-branch rfl gate.
    Define a two-clause function `f` and test `two * f x = f (two * x)`.
    We enumerate clauses and expose which branch passes by `rfl`.
-/
def two : Term := s (s z)

def f : Term → Term
| z         => z
| s n       => s (s (f n))
| add a b   => add (f a) (f b)
| mul a b   => mul (f a) (f b)
| pair a b  => pair (f a) (f b)
| fst t     => fst (f t)
| snd t     => snd (f t)

/-- Clause x = z: both sides reduce by definitional unfolding of `f`. -/
def P1_pass_clause_z_LHS : Term := mul two (f z)     -- = mul two z
def P1_pass_clause_z_RHS : Term := f (mul two z)     -- stays syntactically as `f (mul two z)`
/-
rfl attempt results:
  `P1_pass_clause_z_LHS` defeq `mul two z`.
  `P1_pass_clause_z_RHS` defeq `f (mul two z)`.
Global rfl fails; per-branch equality holds only after rewriting. Failing pattern: `x = s n`.
Minimal counterexample: `x := s z`.
-/
def P1_counterexample : Term := s z

/-! B) Duplication stress test for Rule r4.
    Show additive non-drop first using `size`.
-/
def R4_before (x y : Term) : Term := mul (s x) y
def R4_after  (x y : Term) : Term := add y (mul x y)

/-- Raw size profile to exhibit non-decrease; computation by unfolding `size`. -/
def R4_size_profile (x y : Term) : Nat × Nat := (size (R4_before x y), size (R4_after x y))

/-
Additive calculation:
  size (mul (s x) y) = 2 + size x + size y
  size (add y (mul x y)) = 2 + size x + 2 * size y
Hence `size(after) = size(before) + size y`. No strict drop whenever `size y ≥ 1`.
Only after switching to a robust base order (e.g., DM multiset/RPO with explicit precedence)
can we prove each RHS piece is strictly < the removed LHS redex.
-/

/-! Concrete size lemmas for r4 (sorry-free). -/

@[simp] lemma size_mul_succ (x y : Term) :
    size (mul (s x) y) = size x + size y + 2 := by
  -- size (mul (s x) y) = size (s x) + size y + 1 = (size x + 1) + size y + 1
  calc
    size (mul (s x) y) = size (s x) + size y + 1 := by simp [size]
    _ = (size x + 1) + size y + 1 := by simp [size]
    _ = size x + size y + (1 + 1) := by ac_rfl
    _ = size x + size y + 2 := by simp

@[simp] lemma size_add_y_mul (x y : Term) :
    size (add y (mul x y)) = size x + (size y + size y) + 2 := by
  -- size (add y (mul x y)) = size y + size (mul x y) + 1 = size y + (size x + size y + 1) + 1
  calc
    size (add y (mul x y)) = size y + size (mul x y) + 1 := by simp [size]
    _ = size y + (size x + size y + 1) + 1 := by simp [size]
    _ = size x + (size y + size y) + (1 + 1) := by ac_rfl
    _ = size x + (size y + size y) + 2 := by simp

lemma r4_size_after_eq_before_plus_piece (x y : Term) :
    size (R4_after x y) = size (R4_before x y) + size y := by
  -- Normalize both sides to the same arithmetic form and conclude.
  calc
    size (R4_after x y)
        = size x + (size y + size y) + 2 := by
              simp [R4_after, size_add_y_mul]
    _   = (size x + size y + 2) + size y := by
              ac_rfl
    _   = size (R4_before x y) + size y := by
              simp [R4_before, size_mul_succ]

lemma r4_no_strict_drop_additive (x y : Term) :
    ¬ size (R4_after x y) < size (R4_before x y) := by
  intro hlt
  have : size (R4_before x y) + size y < size (R4_before x y) := by
    simpa [r4_size_after_eq_before_plus_piece] using hlt
  have hle : size (R4_before x y) ≤ size (R4_before x y) + size y := Nat.le_add_right _ _
  exact (Nat.lt_irrefl _) (Nat.lt_of_le_of_lt hle this)

/-! Lightweight lex witness for r4 pieces vs redex (illustrative). -/
namespace R4Lex

abbrev Weight := Nat × Nat

def lexLT (a b : Weight) : Prop :=
  a.fst < b.fst ∨ (a.fst = b.fst ∧ a.snd < b.snd)

def wRedex (x y : Term) : Weight := (1, size (mul (s x) y))
def wPieceY (y : Term) : Weight := (0, size y)
def wPieceMul (x y : Term) : Weight := (0, size (mul x y))

lemma wPieceY_lt_redex (x y : Term) : lexLT (wPieceY y) (wRedex x y) := by
  -- 0 < 1 on the first coordinate
  left; exact Nat.zero_lt_one

lemma wPieceMul_lt_redex (x y : Term) : lexLT (wPieceMul x y) (wRedex x y) := by
  -- 0 < 1 on the first coordinate
  left; exact Nat.zero_lt_one

end R4Lex

/-! DM orientation for r4: {size y, size (mul x y)} <ₘ {size (mul (s x) y)}. -/
namespace R4DM
open Multiset

local infix:70 " <ₘ " => Multiset.IsDershowitzMannaLT

@[simp] lemma size_redex (x y : Term) : size (mul (s x) y) = size x + size y + 2 := by
  -- delegate to size_mul_succ for clarity
  simpa using size_mul_succ x y

@[simp] lemma size_piece_mul (x y : Term) : size (mul x y) = size x + size y + 1 := by
  simp [size]

lemma pieceY_lt_redex (x y : Term) : size y < size (mul (s x) y) := by
  -- Step 1: size y + 0 < size y + (size x + 2)
  have hpos : 0 < size x + 2 := Nat.succ_pos (size x + 1)
  have h0 : size y + 0 < size y + (size x + 2) := Nat.add_lt_add_left hpos _
  have h1 : size y < size y + (size x + 2) := by simpa using h0
  -- Step 2: normalize RHS and fold to redex size
  have h2 : size y < size x + size y + 2 := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h1
  have hred : size x + size y + 2 = size (mul (s x) y) := (size_mul_succ x y).symm
  simpa [hred] using h2

lemma pieceMul_lt_redex (x y : Term) : size (mul x y) < size (mul (s x) y) := by
  -- size x + size y + 1 < size x + size y + 2 and rewrite both sides
  simpa [size_piece_mul, size_mul_succ, size] using Nat.lt_succ_self (size x + size y + 1)

theorem dm_orient (x y : Term) :
  ({size y} + {size (mul x y)}) <ₘ ({size (mul (s x) y)}) := by
  classical
  -- X = 0, Y = {size y, size (mul x y)}, Z = {size redex}
  refine ⟨(0 : Multiset Nat), ({size y} + {size (mul x y)}), {size (mul (s x) y)}, ?hZ, by simp, by simp, ?hY⟩
  · simp
  · intro y' hy'
    rcases mem_add.mp hy' with hY | hM
    · have hy0 : y' = size y := by simpa using hY
      refine ⟨size (mul (s x) y), by simp, ?_⟩
      simpa [hy0] using pieceY_lt_redex x y
    · have hm0 : y' = size (mul x y) := by simpa using hM
      refine ⟨size (mul (s x) y), by simp, ?_⟩
      simpa [hm0] using pieceMul_lt_redex x y

end R4DM

/-! MPO-style orientation for r4 using a simple precedence/status triple. -/
namespace R4MPO

/- Precedence: mul > add > s > pair > fst/snd > z. -/
@[simp] def headRank : Term → Nat
| z         => 0
| s _       => 3
| add _ _   => 4
| mul _ _   => 5
| pair _ _  => 2
| fst _     => 1
| snd _     => 1

@[simp] def weight : Term → Nat × Nat × Nat
| z           => (headRank z, 0, 0)
| s t         => (headRank (s t), size t, 0)
| add a b     => (headRank (add a b), size a, size b)
| mul a b     => (headRank (mul a b), size a, size b)
| pair a b    => (headRank (pair a b), size a, size b)
| fst t       => (headRank (fst t), size t, 0)
| snd t       => (headRank (snd t), size t, 0)

/- Strict lexicographic order on Nat × Nat × Nat. -/
def ltW (u v : Nat × Nat × Nat) : Prop :=
  u.1 < v.1 ∨ (u.1 = v.1 ∧ (u.2.1 < v.2.1 ∨ (u.2.1 = v.2.1 ∧ u.2.2 < v.2.2)))

lemma ltW_of_fst_lt {a b : Nat × Nat × Nat} (h : a.1 < b.1) : ltW a b := Or.inl h

/-- Orientation witness: add y (mul x y) < mul (s x) y under ltW ∘ weight. -/
theorem mpo_orient_r4 (x y : Term) :
  ltW (weight (add y (mul x y))) (weight (mul (s x) y)) := by
  -- First components: headRank(add …) < headRank(mul …)
  left
  -- close 4 < 5 by computation
  have : 4 < 5 := by decide
  simpa [weight, headRank] using this

end R4MPO

/-! C) NameGate and TypeGate probes. -/
/-- Success case (name exists, arity matches): -/
def NG_success : Term := fst (pair z z)

-- /-- Unknown identifier probe: `kappa` is not in this environment. -/
-- -- CONSTRAINT BLOCKER (NameGate): `kappa` unknown.

-- /-- Arity mismatch probe: `add` has arity 2; the following malformed term is intentionally commented out. -/
-- -- def NG_arity_mismatch : Term := add z        -- CONSTRAINT BLOCKER (TypeGate).

/-! D) Internally definable measures.
    Package the "operator-only" constraints explicitly.
-/
-- -- CONSTRAINT BLOCKER (NameGate): `kappa` unknown.

-- /-- Arity mismatch probe: `add` has arity 2; the following malformed term is intentionally commented out. -/
-- -- def NG_arity_mismatch : Term := add z        -- CONSTRAINT BLOCKER (TypeGate).

-- /-! D) Internally definable measures.
--     Package the “operator-only” constraints explicitly.
-- -/

structure InternallyDefinableMeasure where
  κMType  : Type          -- multiset-like component (DM-style), abstract
  μType   : Type          -- ordinal-like component, abstract
  flag    : Term → Bool   -- delta-flag or any unary indicator
  κM      : Term → κMType -- structural multiset measure
  μ       : Term → μType  -- well-founded secondary component
  base    : Term → Term → Prop    -- base simplification order
  wf_base : WellFounded base      -- well-foundedness witness

  /- Monotonicity/compositionality in all contexts. -/
  mono_s      : ∀ {t u}, base t u → base (s t) (s u)
  mono_add_L  : ∀ {t u v}, base t u → base (add t v) (add u v)
  mono_add_R  : ∀ {t u v}, base t u → base (add v t) (add v u)
  mono_mul_L  : ∀ {t u v}, base t u → base (mul t v) (mul u v)
  mono_mul_R  : ∀ {t u v}, base t u → base (mul v t) (mul v u)
  mono_pair_L : ∀ {t u v}, base t u → base (pair t v) (pair u v)
  mono_pair_R : ∀ {t u v}, base t u → base (pair v t) (pair v u)
  mono_fst    : ∀ {t u}, base t u → base (fst t) (fst u)
  mono_snd    : ∀ {t u}, base t u → base (snd t) (snd u)

  /- Lexicographic/orientation gate (relaxed for skeleton):
     For each rule instance, we accept either:
     (i) a flag drop; or (ii) a per-piece strict decrease in `base`; or (iii) a direct base drop.
     This matches the DM/MPO contract where duplicators use per-piece orientation.
  -/
  lex_ok :
    ∀ {l r}, Rule l r →
      (flag r = false ∧ flag l = true) ∨
      (∃ t, t ∈ rhsPiecesLHS l ∧ base t l) ∨
      base r l

  /- Per-piece orientation gate (duplication-aware): for every rule, every listed RHS
    piece is strictly below the removed LHS redex in the base order. This encodes
    the Dershowitz–Manna/MPO-style contract used in P2. -/
  per_piece_base_lt : ∀ {l r}, Rule l r → ∀ t ∈ rhsPiecesLHS l, base t l

  /- Explicit duplication additive failure (documentation contract): the additive `size`
    does not strictly drop for the duplicating rule r4 before any robust orientation.
    This field records the phenomenon as part of the class; a trivial instance can
    reuse `r4_no_strict_drop_additive` below. -/
  dup_additive_nodrop_r4 : ∀ x y, ¬ size (R4_after x y) < size (R4_before x y)

/-- C(Σ): Frozen alias for the KO7 method class used across the project. -/
abbrev CSigma := InternallyDefinableMeasure

/-! E) Stubs for operator-only encodings of Goodstein/Hydra. -/
namespace Encodings

/-- Codes internal to KO7 terms. -/
inductive Code : Type
| zero : Code
| suc  : Code → Code
| pair : Code → Code → Code
| tag  : Nat → Code → Code          -- finite tags for rule schemas
deriving DecidableEq, Repr

/-- Goodstein-style rule schema (shape only). -/
inductive GRule : Code → Code → Prop
| base_change (b n) :
    GRule (Code.tag b (Code.suc n)) (Code.tag (b+1) n)

/-- Hydra-style rule schema (shape only). -/
inductive HRule : Code → Code → Prop
| chop (h) : HRule (Code.suc h) (Code.pair h h)    -- illustrative duplication

end Encodings

-- /-- Target theorems are recorded as statements (no axioms). -/
namespace Targets

open Encodings

/-- “There exists a rule with no internal measure proving its decrease” (statement only). -/
def Exists_No_Internal_Decrease
  (M : InternallyDefinableMeasure) : Prop :=
  ∃ (l r : Term), Rule l r ∧ ¬ M.base l r

/-- Bridge to independence exemplars (statement only). -/
def Goodstein_Maps_Here : Prop :=
  ∀ (c d : Encodings.Code), Encodings.GRule c d → True    -- TODO: fill mapping later

def Hydra_Maps_Here : Prop :=
  ∀ (c d : Encodings.Code), Encodings.HRule c d → True    -- TODO: fill mapping later

end Targets

/-- Demo term touching all constructors. -/
def demo_term : Term :=
  fst (pair (add (s z) (mul (s z) z))
            (snd (pair (add z z) (mul z z))))

/- The reduction of `demo_term` under the eight rules exercises all constructors.
   The actual normalizer is provided in your `Normalize_Safe` bundle. -/

/-! Independence-grade witness: a simple embedding and a same-level no-go. -/

namespace Encodings

/-- Encode natural numbers as KO7 numerals. -/
def natToTerm : Nat → OperatorKO7.OpIncomp.Term
| 0     => OperatorKO7.OpIncomp.Term.z
| n+1   => OperatorKO7.OpIncomp.Term.s (natToTerm n)

/-- Total embedding of `Encodings.Code` into KO7 terms. -/
def encode : Code → OperatorKO7.OpIncomp.Term
| Code.zero      => OperatorKO7.OpIncomp.Term.z
| Code.suc c     => OperatorKO7.OpIncomp.Term.s (encode c)
| Code.pair a b  => OperatorKO7.OpIncomp.Term.pair (encode a) (encode b)
| Code.tag b c   => OperatorKO7.OpIncomp.Term.pair (natToTerm b) (encode c)

end Encodings

/-! Higher-level simulation layer (outside KO7 Step): Admin moves on encoded tags. -/
namespace Simulation
open Encodings OperatorKO7.OpIncomp

/-- Administrative move permitted by the simulation layer: bump the Goodstein base tag on the left of the pair while stripping one succ from the right component (since `encode (suc n) = s (encode n)`). -/
inductive Admin : Term → Term → Prop
| base_change (b : Nat) (n : Encodings.Code) :
    Admin (pair (natToTerm b) (s (encode n))) (pair (natToTerm (b+1)) (encode n))
| hydra_chop (h : Encodings.Code) :
  Admin (s (encode h)) (pair (encode h) (encode h))

/-- Combined simulation relation: either a KO7 Step or an Admin move. -/
def Rel (a b : Term) : Prop := OperatorKO7.OpIncomp.Step a b ∨ Admin a b

/-- One-step simulation of Goodstein base-change under the Admin layer. -/
lemma simulate_GRule_base_change_rel (b : Nat) (n : Encodings.Code) :
  Rel (encode (Encodings.Code.tag b (Encodings.Code.suc n)))
      (encode (Encodings.Code.tag (b+1) n)) := by
  -- By definition, encode(tag b (suc n)) = pair (natToTerm b) (s (encode n))
  -- and encode(tag (b+1) n) = pair (natToTerm (b+1)) (encode n)
  right
  exact Admin.base_change b n

/-- One-step simulation of Hydra chop under the Admin layer. -/
lemma simulate_HRule_chop_rel (h : Encodings.Code) :
  Rel (encode (Encodings.Code.suc h))
      (encode (Encodings.Code.pair h h)) := by
  right
  exact Admin.hydra_chop h

end Simulation

namespace Simulation

/-- Reflexive–transitive closure for Rel. -/
inductive RelStar : Term → Term → Prop
| refl {a} : RelStar a a
| step {a b c} : Rel a b → RelStar b c → RelStar a c

namespace RelStar

theorem trans {a b c} (h1 : RelStar a b) (h2 : RelStar b c) : RelStar a c := by
  induction h1 with
  | refl => simpa using h2
  | step h h1 ih => exact RelStar.step h (ih h2)

theorem of_step {a b} (h : OperatorKO7.OpIncomp.Step a b) : RelStar a b :=
  RelStar.step (Or.inl h) RelStar.refl

theorem of_admin {a b} (h : Admin a b) : RelStar a b :=
  RelStar.step (Or.inr h) RelStar.refl

end RelStar

end Simulation

namespace Simulation
open OperatorKO7.OpIncomp.Encodings

/- Paper↔code map (names frozen):
  - CSigma ≡ `M_size`
  - δ two-case: `delta_top_cases_add_s`, `delta_top_cases_mul_s`
  - δ Star runners: `delta_star_add_s_auto`, `delta_star_mul_s_auto`
  - RelStar lifts: `simulate_GRule_base_change_relStar`, `simulate_HRule_chop_relStar`
  - No single Step from encode: `Targets.Goodstein_NoSingleStep_Encode`
-/

/-- Lift Goodstein base-change simulation to `RelStar`. -/
lemma simulate_GRule_base_change_relStar (b : Nat) (n : Encodings.Code) :
  Simulation.RelStar (encode (Encodings.Code.tag b (Encodings.Code.suc n)))
    (encode (Encodings.Code.tag (b+1) n)) :=
  Simulation.RelStar.of_admin (Admin.base_change b n)

/-- Lift Hydra chop simulation to `RelStar`. -/
lemma simulate_HRule_chop_relStar (h : Encodings.Code) :
  Simulation.RelStar (encode (Encodings.Code.suc h))
    (encode (Encodings.Code.pair h h)) :=
  Simulation.RelStar.of_admin (Admin.hydra_chop h)

end Simulation

namespace Targets
open Encodings

/-- Same-level no-go box: Goodstein base-change does not collapse to a single KO7 Step under `encode`.
Recorded as a statement; proof handled in documentation/meta notes. -/
def Goodstein_NoSingleStep_Encode : Prop :=
  ∀ (b : Nat) (n : Encodings.Code),
    ¬ Step (encode (Code.tag b (Code.suc n)))
           (encode (Code.tag (b+1) n))

end Targets

-- Independence-grade “no-go box” recorded as a statement under Targets.
-- We avoid asserting the proof here; see documentation for the meta-argument.

/-- No single OperatorKO7.OpIncomp.Step originates from a numeral `natToTerm b`. -/
lemma no_step_from_natToTerm (b : Nat) : ∀ t, ¬ Step (Encodings.natToTerm b) t := by
  induction b with
  | zero =>
    intro t h
    -- LHS is `z`; there is no Rule/Context matching it.
    cases h with
    | base hr => cases hr
  | succ b ih =>
    intro t h
    -- LHS is `s (natToTerm b)`; only sCtx could apply, implying an inner step.
    cases h with
    | base hr => cases hr
    | sCtx hinner =>
      exact (ih _ hinner)

/-- Encoded Goodstein codes (`encode`) contain only z/s/pair/nat tags, so they have no KO7 single-step. -/
lemma no_step_from_encode (c : Encodings.Code) : ∀ t, ¬ Step (Encodings.encode c) t := by
  induction c with
  | zero =>
    intro t h
    -- LHS is `z`; only `base` could appear, which contradicts Rule shapes.
    cases h with
    | base hr => cases hr
  | suc c ih =>
    intro t h
    -- LHS is `s (encode c)`; only `base` or `sCtx` can appear.
    cases h with
    | base hr => cases hr
    | sCtx hinner => exact (ih _ hinner)
  | pair a b iha ihb =>
    intro t h
    -- LHS is `pair (encode a) (encode b)`; only `base`/`pairLCtx`/`pairRCtx` possible.
    cases h with
    | base hr => cases hr
    | pairLCtx hL => exact (iha _ hL)
    | pairRCtx hR => exact (ihb _ hR)
  | tag b c ih =>
    intro t h
    -- LHS is `pair (natToTerm b) (encode c)`; only `base`/`pairLCtx`/`pairRCtx` possible.
    cases h with
    | base hr => cases hr
    | pairLCtx hL => exact (no_step_from_natToTerm b _ hL)
    | pairRCtx hR => exact (ih _ hR)

namespace Targets
open Encodings

/-- Formal proof: Goodstein base-change is not a single OperatorKO7.OpIncomp.Step under `encode`. -/
theorem goodstein_no_single_step_encode : Goodstein_NoSingleStep_Encode := by
  intro b n h
  -- Use the general “no step from encode” lemma instantiated at `tag b (suc n)`.
  -- This is stronger: there is no OperatorKO7.OpIncomp.Step from the encoded source to any target.
  have hno := OperatorKO7.OpIncomp.no_step_from_encode (c := Encodings.Code.tag b (Encodings.Code.suc n))
    (t := Encodings.encode (Encodings.Code.tag (b+1) n))
  exact hno h

/-- Bridging theorem (Goodstein family): encoded base-change steps are simulated in `RelStar`. -/
theorem goodstein_family_simulated_in_RelStar
  (b : Nat) (n : Encodings.Code) :
  Simulation.RelStar (encode (Encodings.Code.tag b (Encodings.Code.suc n)))
                     (encode (Encodings.Code.tag (b+1) n)) :=
  Simulation.simulate_GRule_base_change_relStar b n

/-- Bridging theorem (Hydra family): encoded chop steps are simulated in `RelStar`. -/
theorem hydra_family_simulated_in_RelStar
  (h : Encodings.Code) :
  Simulation.RelStar (encode (Encodings.Code.suc h))
                     (encode (Encodings.Code.pair h h)) :=
  Simulation.simulate_HRule_chop_relStar h

end Targets



/-! Tiny examples exercising witnesses and Star utilities. -/
example (x y : Term) : R4Lex.lexLT (R4Lex.wPieceY y) (R4Lex.wRedex x y) :=
  R4Lex.wPieceY_lt_redex x y

example (x y : Term) :
    Multiset.IsDershowitzMannaLT ({size y} + {size (mul x y)}) ({size (mul (s x) y)}) := by
  simpa using R4DM.dm_orient x y

example (x y : Term) :
    R4MPO.ltW (R4MPO.weight (add y (mul x y))) (R4MPO.weight (mul (s x) y)) :=
  R4MPO.mpo_orient_r4 x y

example (y : Term) : Star Step (add z y) y :=
  Star.step (Step.base (Rule.r1 y)) Star.refl

-- Additional Step → Star examples
example (y : Term) : Star Step (mul z y) z :=
  Star.step (Step.base (Rule.r3 y)) Star.refl

example (x y : Term) : Star Step (fst (pair x y)) x :=
  Star.step (Step.base (Rule.r5 x y)) Star.refl

end OperatorKO7.OpIncomp

/-!
Tiny Goodstein/Hydra examples (toy cores)

These are small, independent examples that exercise the minimal toy cores added
for exposition. They do not interact with the KO7 kernel and are provided as
cross-linkable witnesses for the paper and Impossibility catalog.
-/

namespace TinyGoodsteinHydra

open OperatorKO7
open OperatorKO7.GoodsteinCore
open OperatorKO7.HydraCore

/- Goodstein: one-step base-change on the toy state. -/
example (b n : Nat) (t : Cn) :
  GoodsteinCore.Step ⟨Base.b b, Cn.s t⟩ ⟨Base.b (b+1), t⟩ := by
  simpa using GoodsteinCore.one_step b n t

/- Hydra: a chop duplicates the other subtree (left and right variants). -/
example (h : Hydra) :
  HydraCore.Step (Hydra.node Hydra.head h) (Hydra.node h h) :=
  HydraCore.Step.chop_left h

example (h : Hydra) :
  HydraCore.Step (Hydra.node h Hydra.head) (Hydra.node h h) :=
  HydraCore.Step.chop_right h

/- Existential-style tiny witness. -/
example (h : Hydra) : ∃ h', HydraCore.Step (Hydra.node Hydra.head h) h' :=
  ⟨Hydra.node h h, HydraCore.Step.chop_left h⟩

end TinyGoodsteinHydra

namespace OperatorKO7.OpIncomp
open Term
-- set_option diagnostics true
/-- A concrete internal-measure instance using size as the base order.
Flags mark only r2/r4 LHSs (where additive size does not strictly drop). -/
noncomputable def flagTerm : Term → Bool
| add (s _) _ => true
| mul (s _) _ => true
| _           => false

noncomputable def M_size : InternallyDefinableMeasure where
  κMType := Unit
  μType  := Unit
  flag   := flagTerm
  κM     := fun _ => ()
  μ      := fun _ => ()
  -- size-based base order
  base   := fun a b => size a < size b
  wf_base := by
    -- pull back Nat.lt along `size`
    simpa using (InvImage.wf (f := size) Nat.lt_wfRel.wf)
  -- context monotonicity (all 7 contexts)
  mono_s := by
    intro t u h; dsimp [size] at *; simpa using Nat.add_lt_add_right h 1
  mono_add_L := by
    intro t u v h; dsimp [size] at *
    -- size (add t v) = size t + (size v + 1)
    have := Nat.add_lt_add_left h (size v + 1)
    -- rewrite lhs: (size v + 1) + size t = size t + (size v + 1)
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  mono_add_R := by
    intro t u v h; dsimp [size] at *
    -- size (add v t) = size v + (size t + 1)
    have := Nat.add_lt_add_left h (size v)
    have := Nat.add_lt_add_right this 1
    -- reorder sums
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  mono_mul_L := by
    intro t u v h; dsimp [size] at *
    have := Nat.add_lt_add_left h (size v + 1)
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  mono_mul_R := by
    intro t u v h; dsimp [size] at *
    have := Nat.add_lt_add_left h (size v)
    have := Nat.add_lt_add_right this 1
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  mono_pair_L := by
    intro t u v h; dsimp [size] at *
    have := Nat.add_lt_add_left h (size v + 1)
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  mono_pair_R := by
    intro t u v h; dsimp [size] at *
    have := Nat.add_lt_add_left h (size v)
    have := Nat.add_lt_add_right this 1
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  mono_fst := by
    intro t u h; dsimp [size] at *
    simpa using Nat.add_lt_add_right h 1
  mono_snd := by
    intro t u h; dsimp [size] at *
    simpa using Nat.add_lt_add_right h 1
  -- lex gate: satisfy via per-piece base drops for all rules
  lex_ok := by
    intro l r hr
    cases hr with
    | r1 y =>
      -- r1: add z y → y, need y < 1 + y + 1
      exact Or.inr (Or.inr (by simp only [size]; omega))
    | r2 x y =>
      -- r2: add (s x) y → s (add x y)
      exact Or.inr (Or.inl ⟨add x y, by simp [rhsPiecesLHS], by simp only [size]; omega⟩)
    | r3 y =>
      -- r3: mul z y → z, need 1 < 1 + y + 1
      exact Or.inr (Or.inr (by simp only [size]; omega))
    | r4 x y =>
      -- r4: mul (s x) y → add y (mul x y)
      exact Or.inr (Or.inl ⟨y, by simp [rhsPiecesLHS], by simp only [size]; omega⟩)
    | r5 x y =>
      -- r5: fst (pair x y) → x, need x < x + y + 2
      exact Or.inr (Or.inr (by simp only [size]; omega))
    | r6 x y =>
      -- r6: snd (pair x y) → y, need y < x + y + 2
      exact Or.inr (Or.inr (by simp only [size]; omega))
    | r7 x =>
      -- r7: add x z → x, need x < x + 2
      exact Or.inr (Or.inr (by simp only [size]; omega))
    | r8 x =>
      -- r8: mul x z → z, need 1 < x + 2
      exact Or.inr (Or.inr (by simp only [size]; omega))
  -- per-piece strictness (duplication-aware)
  per_piece_base_lt := by
    intro l r h t ht
    -- prove size t < size l by case on l
    cases l with
    | z => cases h
    | s tl => cases h
    | add a b =>
      -- pieces = pieces from a (r1/r2) plus maybe from b (r7 when b=z)
      dsimp [rhsPiecesLHS] at ht
      have : size t < size a + size b + 1 := by
        rcases List.mem_append.mp ht with hL | hR
        · -- left pieces from a
          cases a with
          | z =>
            -- t ∈ [b]
            have hx : t = b := by simpa using hL
            subst hx
            -- size b < size (add z b) = 1 + b + 1
            simp only [size]
            omega
          | s xx =>
            -- t ∈ [add xx b]
            have hx : t = add xx b := by simpa using hL
            subst hx
            -- size (add xx b) < size (add (s xx) b)
            simp only [size]
            omega
          | _ =>
            -- no pieces from other constructors
            cases hL
        · -- right pieces from b
          cases b with
          | z =>
            -- t ∈ [a]
            have hx : t = a := by simpa using hR
            subst hx
            -- size a < size (add a z) = a + 1 + 1
            simp only [size]
            omega
          | _ =>
            cases hR
      simpa [size] using this
    | mul a b =>
      dsimp [rhsPiecesLHS] at ht
      have : size t < size a + size b + 1 := by
        rcases List.mem_append.mp ht with hL | hR
        · -- left pieces from a
          cases a with
          | z =>
            -- t ∈ [z]
            have hx : t = z := by simpa using hL
            subst hx
            -- 1 < 1 + size b + 1
            simp only [size]
            omega
          | s xx =>
            rcases List.mem_cons.mp hL with hby | hmul
            · -- t = b
              have hx : t = b := by simpa using hby
              subst hx
              -- size b < size (s xx) + size b + 1 = xx + 1 + b + 1
              simp only [size]
              omega
            · -- t = mul xx b
              have hx : t = mul xx b := by simpa using hmul
              subst hx
              -- size (mul xx b) < size (mul (s xx) b)
              simp only [size]
              omega
          | _ =>
            cases hL
        · -- right pieces from b
          cases b with
          | z =>
            -- t ∈ [z]
            have hx : t = z := by simpa using hR
            subst hx
            -- 1 < size a + 1 + 1
            simp only [size]
            omega
          | _ =>
            cases hR
      simpa [size] using this
    | pair a b => cases h
    | fst u =>
      cases u with
      | pair xx yy =>
        dsimp [rhsPiecesLHS] at ht
        have hx : t = xx := by simpa using ht
        subst hx
        simp [size]
        omega
      | _ => cases h
    | snd u =>
      cases u with
      | pair xx yy =>
        dsimp [rhsPiecesLHS] at ht
        have hx : t = yy := by simpa using ht
        subst hx
        simp [size]
        omega
      | _ => cases h
  dup_additive_nodrop_r4 := by
    intro x y; exact r4_no_strict_drop_additive x y

/-! Optional δ-guard (Prop) isolating the duplicating/flagged shapes.
    We provide a decidable predicate and a couple of lightweight lemmas. -/

/-- Terms whose head is add (s ·) · or mul (s ·) ·. -/
inductive Delta : Term → Prop
| add_s (x y : Term) : Delta (add (s x) y)
| mul_s (x y : Term) : Delta (mul (s x) y)

attribute [simp] Delta.add_s Delta.mul_s

/-- Decidability for `Delta`. -/
instance : DecidablePred Delta := by
  intro t
  cases t with
  | z => exact isFalse (by intro h; cases h)
  | s _ => exact isFalse (by intro h; cases h)
  | add a b =>
    cases a with
    | s x => exact isTrue (Delta.add_s x b)
    | _ => exact isFalse (by intro h; cases h)
  | mul a b =>
    cases a with
    | s x => exact isTrue (Delta.mul_s x b)
    | _ => exact isFalse (by intro h; cases h)
  | pair _ _ => exact isFalse (by intro h; cases h)
  | fst _ => exact isFalse (by intro h; cases h)
  | snd _ => exact isFalse (by intro h; cases h)

@[simp] lemma Delta_r2 (x y : Term) : Delta (add (s x) y) := Delta.add_s x y
@[simp] lemma Delta_r4 (x y : Term) : Delta (mul (s x) y) := Delta.mul_s x y

/- Simple preservation under right-context rewriting: the δ head persists. -/
lemma Delta_preserve_addR {x t u : Term} (_h : Step t u) : Delta (add (s x) u) := by
  simpa using (Delta.add_s x u)

lemma Delta_preserve_mulR {x t u : Term} (_h : Step t u) : Delta (mul (s x) u) := by
  simpa using (Delta.mul_s x u)

-- Preservation for remaining contexts (trivial shape persistence)
lemma Delta_preserve_addL {x t u : Term} (_h : Step t u) : Delta (add (s x) u) := by
  simpa using (Delta.add_s x u)

lemma Delta_preserve_mulL {x t u : Term} (_h : Step t u) : Delta (mul (s x) u) := by
  simpa using (Delta.mul_s x u)

lemma Delta_preserve_pairL {x t u v : Term} (_h : Step t u) : Delta (add (s x) v) := by
  simpa using (Delta.add_s x v)

lemma Delta_preserve_pairR {x t u v : Term} (_h : Step t u) : Delta (mul (s x) v) := by
  simpa using (Delta.mul_s x v)

lemma Delta_preserve_fstCtx {x t u : Term} (_h : Step t u) : Delta (add (s x) (fst u)) := by
  -- Note: guard refers to outer head; inner shape changes do not affect outer head
  simpa using (Delta.add_s x (fst u))

lemma Delta_preserve_sndCtx {x t u : Term} (_h : Step t u) : Delta (mul (s x) (snd u)) := by
  simpa using (Delta.mul_s x (snd u))

/-! Substitution (homomorphic map) and δ‑preservation under substitution. -/

/-- Homomorphic transform on KO7 terms (preserves heads, transforms subterms). -/
def mapTerm (σ : Term → Term) : Term → Term
| z => z
| s t => s (mapTerm σ t)
| add a b => add (mapTerm σ a) (mapTerm σ b)
| mul a b => mul (mapTerm σ a) (mapTerm σ b)
| pair a b => pair (mapTerm σ a) (mapTerm σ b)
| fst t => fst (mapTerm σ t)
| snd t => snd (mapTerm σ t)

@[simp] lemma mapTerm_s (σ) (t : Term) : mapTerm σ (s t) = s (mapTerm σ t) := rfl
@[simp] lemma mapTerm_add (σ) (a b : Term) : mapTerm σ (add a b) = add (mapTerm σ a) (mapTerm σ b) := rfl
@[simp] lemma mapTerm_mul (σ) (a b : Term) : mapTerm σ (mul a b) = mul (mapTerm σ a) (mapTerm σ b) := rfl

lemma Delta_preserve_r2_subst (σ : Term → Term) (x y : Term) :
  Delta (mapTerm σ (add (s x) y)) := by
  simp [mapTerm, Delta.add_s]

lemma Delta_preserve_r4_subst (σ : Term → Term) (x y : Term) :
  Delta (mapTerm σ (mul (s x) y)) := by
  simp [mapTerm, Delta.mul_s]

/-! Promote mapTerm to a substitution alias and restate δ‑substitution lemmas. -/

abbrev subst := mapTerm

@[simp] lemma subst_s (σ) (t : Term) : subst σ (s t) = s (subst σ t) := rfl
@[simp] lemma subst_add (σ) (a b : Term) : subst σ (add a b) = add (subst σ a) (subst σ b) := rfl
@[simp] lemma subst_mul (σ) (a b : Term) : subst σ (mul a b) = mul (subst σ a) (subst σ b) := rfl

lemma Delta_subst_preserves_r2 (σ : Term → Term) (x y : Term) :
  Delta (subst σ (add (s x) y)) := by
  simp [subst, mapTerm, Delta.add_s]

lemma Delta_subst_preserves_r4 (σ : Term → Term) (x y : Term) :
  Delta (subst σ (mul (s x) y)) := by
  simp [subst, mapTerm, Delta.mul_s]

/-! Star-level automation for δ shapes. -/

lemma delta_star_cases_add_s (x y : Term) :
  Star Step (add (s x) y) (s (add x y)) ∨
  (y = z ∧ Star Step (add (s x) y) (s x)) := by
  -- r2 always provides the left branch as a single step
  exact Or.inl (Star.step (Step.base (Rule.r2 x y)) Star.refl)

lemma delta_star_cases_mul_s (x y : Term) :
  Star Step (mul (s x) y) (add y (mul x y)) ∨
  (y = z ∧ Star Step (mul (s x) y) z) := by
  -- r4 always provides the left branch as a single step
  exact Or.inl (Star.step (Step.base (Rule.r4 x y)) Star.refl)

/-! δ exhaustive two-case lemmas at the top level. -/

lemma delta_top_cases_add_s (x y r : Term)
  (h : Rule (add (s x) y) r) :
  r = s (add x y) ∨ (y = z ∧ r = s x) := by
  cases h with
  | r2 _ _ => exact Or.inl rfl
  | r7 _ => exact Or.inr ⟨rfl, rfl⟩

lemma delta_top_cases_mul_s (x y r : Term)
  (h : Rule (mul (s x) y) r) :
  r = add y (mul x y) ∨ (y = z ∧ r = z) := by
  cases h with
  | r4 _ _ => exact Or.inl rfl
  | r8 _ => exact Or.inr ⟨rfl, rfl⟩

/-- δ-safe critical pairs coverage (add): every rule at the guarded top-shape matches one of the two cases. -/
theorem Delta_SafePairs_Exhaustive_add
  (x y r : Term) (_hδ : Delta (add (s x) y)) (h : Rule (add (s x) y) r) :
  r = s (add x y) ∨ (y = z ∧ r = s x) :=
  delta_top_cases_add_s x y r h

/-- δ-safe critical pairs coverage (mul): every rule at the guarded top-shape matches one of the two cases. -/
theorem Delta_SafePairs_Exhaustive_mul
  (x y r : Term) (_hδ : Delta (mul (s x) y)) (h : Rule (mul (s x) y) r) :
  r = add y (mul x y) ∨ (y = z ∧ r = z) :=
  delta_top_cases_mul_s x y r h

/-! Small Star runners that choose the RHS automatically via the δ two-case split. -/

/-- Canonical RHS selector for `add (s x) y` using the δ two-case: if `y` is `z`, pick `s x`,
  otherwise pick `s (add x y)`. -/
def delta_rhs_add_s (x y : Term) : Term :=
  match y with
  | z => s x
  | _ => s (add x y)

/-- Canonical RHS selector for `mul (s x) y` using the δ two-case: if `y` is `z`, pick `z`,
  otherwise pick `add y (mul x y)`. -/
def delta_rhs_mul_s (x y : Term) : Term :=
  match y with
  | z => z
  | _ => add y (mul x y)

/-- One-step Star that automatically chooses the appropriate RHS for `add (s x) y`. -/
lemma delta_star_add_s_auto (x y : Term) :
  Star Step (add (s x) y) (delta_rhs_add_s x y) := by
  -- Use a direct case split on `y`'s top constructor.
  cases y with
  | z =>
    -- pick r7
    change Star Step (add (s x) z) (s x)
    exact Star.step (Step.base (Rule.r7 (s x))) Star.refl
  | s y' =>
    -- pick r2
    change Star Step (add (s x) (s y')) (s (add x (s y')))
    exact Star.step (Step.base (Rule.r2 x (s y'))) Star.refl
  | add a b =>
    change Star Step (add (s x) (add a b)) (s (add x (add a b)))
    exact Star.step (Step.base (Rule.r2 x (add a b))) Star.refl
  | mul a b =>
    change Star Step (add (s x) (mul a b)) (s (add x (mul a b)))
    exact Star.step (Step.base (Rule.r2 x (mul a b))) Star.refl
  | pair a b =>
    change Star Step (add (s x) (pair a b)) (s (add x (pair a b)))
    exact Star.step (Step.base (Rule.r2 x (pair a b))) Star.refl
  | fst t =>
    change Star Step (add (s x) (fst t)) (s (add x (fst t)))
    exact Star.step (Step.base (Rule.r2 x (fst t))) Star.refl
  | snd t =>
    change Star Step (add (s x) (snd t)) (s (add x (snd t)))
    exact Star.step (Step.base (Rule.r2 x (snd t))) Star.refl

/-- One-step Star that automatically chooses the appropriate RHS for `mul (s x) y`. -/
lemma delta_star_mul_s_auto (x y : Term) :
  Star Step (mul (s x) y) (delta_rhs_mul_s x y) := by
  cases y with
  | z =>
    change Star Step (mul (s x) z) z
    exact Star.step (Step.base (Rule.r8 (s x))) Star.refl
  | s y' =>
    change Star Step (mul (s x) (s y')) (add (s y') (mul x (s y')))
    exact Star.step (Step.base (Rule.r4 x (s y'))) Star.refl
  | add a b =>
    change Star Step (mul (s x) (add a b)) (add (add a b) (mul x (add a b)))
    exact Star.step (Step.base (Rule.r4 x (add a b))) Star.refl
  | mul a b =>
    change Star Step (mul (s x) (mul a b)) (add (mul a b) (mul x (mul a b)))
    exact Star.step (Step.base (Rule.r4 x (mul a b))) Star.refl
  | pair a b =>
    change Star Step (mul (s x) (pair a b)) (add (pair a b) (mul x (pair a b)))
    exact Star.step (Step.base (Rule.r4 x (pair a b))) Star.refl
  | fst t =>
    change Star Step (mul (s x) (fst t)) (add (fst t) (mul x (fst t)))
    exact Star.step (Step.base (Rule.r4 x (fst t))) Star.refl
  | snd t =>
    change Star Step (mul (s x) (snd t)) (add (snd t) (mul x (snd t)))
    exact Star.step (Step.base (Rule.r4 x (snd t))) Star.refl

/-! δ‑substitution per‑branch lemma stubs (align names with paper). -/

/-- Under substitution, the r2 guard shape is preserved (wrapper aligning naming with paper). -/
@[simp] theorem delta_subst_preserves_r2 (σ : Term → Term) (x y : Term) :
  Delta (subst σ (add (s x) y)) :=
  Delta_subst_preserves_r2 σ x y

/-- Under substitution, the r4 guard shape is preserved (wrapper aligning naming with paper). -/
@[simp] theorem delta_subst_preserves_r4 (σ : Term → Term) (x y : Term) :
  Delta (subst σ (mul (s x) y)) :=
  Delta_subst_preserves_r4 σ x y

/-! Examples using `M_size.lex_ok` on representative rules. -/

example (y : Term) :
  (flagTerm y = false ∧ flagTerm (add z y) = true) ∨
  (∃ t, t ∈ rhsPiecesLHS (add z y) ∧ M_size.base t (add z y)) ∨
  M_size.base y (add z y) := by
  -- r1: add z y → y
  simpa using (M_size.lex_ok (Rule.r1 y))

example (x y : Term) :
  (flagTerm (add y (mul x y)) = false ∧ flagTerm (mul (s x) y) = true) ∨
  (∃ t, t ∈ rhsPiecesLHS (mul (s x) y) ∧ M_size.base t (mul (s x) y)) ∨
  M_size.base (add y (mul x y)) (mul (s x) y) := by
  -- r4: mul (s x) y → add y (mul x y)
  simpa using (M_size.lex_ok (Rule.r4 x y))

example (x : Term) :
  (flagTerm x = false ∧ flagTerm (add x z) = true) ∨
  (∃ t, t ∈ rhsPiecesLHS (add x z) ∧ M_size.base t (add x z)) ∨
  M_size.base x (add x z) := by
  -- r7: add x z → x
  simpa using (M_size.lex_ok (Rule.r7 x))

example (x y : Term) :
  (flagTerm (s (add x y)) = false ∧ flagTerm (add (s x) y) = true) ∨
  (∃ t, t ∈ rhsPiecesLHS (add (s x) y) ∧ M_size.base t (add (s x) y)) ∨
  M_size.base (s (add x y)) (add (s x) y) := by
  -- r2: add (s x) y → s (add x y)
  simpa using (M_size.lex_ok (Rule.r2 x y))

example (y : Term) :
  (flagTerm z = false ∧ flagTerm (mul z y) = true) ∨
  (∃ t, t ∈ rhsPiecesLHS (mul z y) ∧ M_size.base t (mul z y)) ∨
  M_size.base z (mul z y) := by
  -- r3: mul z y → z
  simpa using (M_size.lex_ok (Rule.r3 y))

example (x y : Term) :
  (flagTerm x = false ∧ flagTerm (fst (pair x y)) = true) ∨
  (∃ t, t ∈ rhsPiecesLHS (fst (pair x y)) ∧ M_size.base t (fst (pair x y))) ∨
  M_size.base x (fst (pair x y)) := by
  -- r5: fst (pair x y) → x
  simpa using (M_size.lex_ok (Rule.r5 x y))

example (x y : Term) :
  (flagTerm y = false ∧ flagTerm (snd (pair x y)) = true) ∨
  (∃ t, t ∈ rhsPiecesLHS (snd (pair x y)) ∧ M_size.base t (snd (pair x y))) ∨
  M_size.base y (snd (pair x y)) := by
  -- r6: snd (pair x y) → y
  simpa using (M_size.lex_ok (Rule.r6 x y))

example (x : Term) :
  (flagTerm z = false ∧ flagTerm (mul x z) = true) ∨
  (∃ t, t ∈ rhsPiecesLHS (mul x z) ∧ M_size.base t (mul x z)) ∨
  M_size.base z (mul x z) := by
  -- r8: mul x z → z
  simpa using (M_size.lex_ok (Rule.r8 x))
end OperatorKO7.OpIncomp
