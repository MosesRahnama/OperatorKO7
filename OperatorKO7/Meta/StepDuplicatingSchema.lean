import Mathlib

/-!
# Generic Step-Duplicating Schema

This module isolates the abstract shape used by the KO7 / RecΔ-core impossibility
proofs:

- a base term,
- a successor constructor,
- a binary wrapper constructor, and
- a ternary recursor with duplicating successor step
  `recur b s (succ n) ↦ wrap s (recur b s n)`.

The point is to prove the direct/compositional impossibility theorems once at the
schema level, independent of KO7's surrounding signature.
-/

namespace OperatorKO7.StepDuplicating

/-- Minimal constructor interface needed for the duplication barrier. -/
structure StepDuplicatingSchema where
  T : Type
  base : T
  succ : T → T
  wrap : T → T → T
  recur : T → T → T → T

namespace StepDuplicatingSchema

/-- Left-nested wrapper chain used to pump additive measures. -/
def wrapIter (S : StepDuplicatingSchema) : Nat → S.T
  | 0 => S.base
  | k + 1 => S.wrap (wrapIter S k) S.base

/-- Successor chain used to pump affine measures with positive successor drift. -/
def succIter (S : StepDuplicatingSchema) : Nat → S.T
  | 0 => S.base
  | k + 1 => S.succ (succIter S k)

/-- Additive compositional measures on a step-duplicating schema. -/
structure AdditiveMeasure (S : StepDuplicatingSchema) where
  eval : S.T → Nat
  w_base : Nat
  w_succ : Nat
  w_wrap : Nat
  w_recur : Nat
  eval_base : eval S.base = w_base
  eval_succ : ∀ t, eval (S.succ t) = w_succ + eval t
  eval_wrap : ∀ x y, eval (S.wrap x y) = w_wrap + eval x + eval y
  eval_recur : ∀ b s n, eval (S.recur b s n) = w_recur + eval b + eval s + eval n
  h_wrap_pos : w_wrap ≥ 1

/-- The wrapper pump grows at least linearly because `wrap` has positive weight. -/
lemma eval_wrapIter_ge {S : StepDuplicatingSchema} (M : AdditiveMeasure S) (k : Nat) :
    M.eval (wrapIter S k) ≥ k := by
  induction k with
  | zero =>
      rw [wrapIter, M.eval_base]
      omega
  | succ k ih =>
      simp [wrapIter, M.eval_wrap, M.eval_base]
      have := M.h_wrap_pos
      omega

/-- Schema-level Tier 1 impossibility:
no additive compositional measure can orient the duplicating step uniformly. -/
theorem no_additive_orients_dup_step {S : StepDuplicatingSchema} (M : AdditiveMeasure S) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  intro h
  have hspec := h S.base (wrapIter S M.w_succ) S.base
  have hge := eval_wrapIter_ge M M.w_succ
  simp [M.eval_base, M.eval_succ, M.eval_wrap, M.eval_recur] at hspec
  have := M.h_wrap_pos
  omega

/-- Constructor-local affine measures with no cross terms between arguments. -/
structure AffineMeasure (S : StepDuplicatingSchema) where
  eval : S.T → Nat
  c_base : Nat
  succ_bias : Nat
  succ_scale : Nat
  wrap_const : Nat
  wrap_left : Nat
  wrap_right : Nat
  recur_const : Nat
  recur_base : Nat
  recur_step : Nat
  recur_counter : Nat
  eval_base : eval S.base = c_base
  eval_succ : ∀ t, eval (S.succ t) = succ_bias + succ_scale * eval t
  eval_wrap : ∀ x y, eval (S.wrap x y) = wrap_const + wrap_left * eval x + wrap_right * eval y
  eval_recur :
    ∀ b s n,
      eval (S.recur b s n) =
        recur_const + recur_base * eval b + recur_step * eval s + recur_counter * eval n
  h_wrap_left_pos : 1 ≤ wrap_left
  h_wrap_right_pos : 1 ≤ wrap_right

/-- Unbounded range hypothesis for schema-level affine impossibility theorems. -/
def HasUnboundedRange {S : StepDuplicatingSchema} (M : AffineMeasure S) : Prop :=
  ∀ k : Nat, ∃ t : S.T, k ≤ M.eval t

/-- Positive affine successor drift gives a linear pump along `succIter`. -/
lemma eval_succIter_ge {S : StepDuplicatingSchema} (M : AffineMeasure S)
    (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale) (k : Nat) :
    k ≤ M.eval (succIter S k) := by
  induction k with
  | zero =>
      rw [succIter, M.eval_base]
      omega
  | succ k ih =>
      simp [succIter, M.eval_succ]
      nlinarith

/-- Positive affine wrap drift from `base` gives a linear pump along `wrapIter`. -/
lemma eval_wrapIter_ge_affine {S : StepDuplicatingSchema} (M : AffineMeasure S)
    (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base) (k : Nat) :
    k ≤ M.eval (wrapIter S k) := by
  induction k with
  | zero =>
      rw [wrapIter, M.eval_base]
      omega
  | succ k ih =>
      simp [wrapIter, M.eval_wrap, M.eval_base]
      nlinarith [M.h_wrap_left_pos, h_wrap_bias, ih]

/-- Schema-level affine/linear barrier:
any affine measure with positive wrapper sensitivity and unbounded attainable values
fails on the duplicating step. -/
theorem no_affine_orients_dup_step_of_unbounded
    {S : StepDuplicatingSchema} (M : AffineMeasure S) (hunbounded : HasUnboundedRange M) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  intro h
  let threshold := M.recur_counter * (M.succ_bias + M.succ_scale * M.c_base)
  rcases hunbounded threshold with ⟨s, hs⟩
  let Sval := M.eval s
  let A := M.recur_const + M.recur_base * M.c_base + M.recur_step * Sval
  let B := M.recur_counter * M.c_base
  let T := M.recur_counter * (M.succ_bias + M.succ_scale * M.c_base)
  have hspec := h S.base s S.base
  have hspec' :
      M.wrap_const + M.wrap_left * Sval + M.wrap_right * (A + B) < A + T := by
    simpa [Sval, A, B, T, M.eval_base, M.eval_succ, M.eval_wrap, M.eval_recur,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.mul_add] using hspec
  have hsT : T ≤ Sval := by
    simpa [T, threshold, Sval] using hs
  have hS : Sval ≤ M.wrap_left * Sval := by
    calc
      Sval = 1 * Sval := by simp
      _ ≤ M.wrap_left * Sval := by
        exact Nat.mul_le_mul_right Sval M.h_wrap_left_pos
  have hAB : A + B ≤ M.wrap_right * (A + B) := by
    calc
      A + B = 1 * (A + B) := by simp
      _ ≤ M.wrap_right * (A + B) := by
        exact Nat.mul_le_mul_right (A + B) M.h_wrap_right_pos
  have h_rhs_to_aS : A + T ≤ A + Sval := Nat.add_le_add_left hsT A
  have h_aS_to_aWS : A + Sval ≤ A + M.wrap_left * Sval := Nat.add_le_add_left hS A
  have h_aWS_to_sum : A + M.wrap_left * Sval ≤ A + M.wrap_left * Sval + B := by
    exact Nat.le_add_right _ _
  have h_sum_to_wsum :
      A + M.wrap_left * Sval + B ≤ M.wrap_left * Sval + M.wrap_right * (A + B) := by
    have hAB' :
        M.wrap_left * Sval + (A + B) ≤ M.wrap_left * Sval + M.wrap_right * (A + B) :=
      Nat.add_le_add_left hAB (M.wrap_left * Sval)
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hAB'
  have h_with_const :
      M.wrap_left * Sval + M.wrap_right * (A + B) ≤
        M.wrap_const + M.wrap_left * Sval + M.wrap_right * (A + B) := by
    calc
      M.wrap_left * Sval + M.wrap_right * (A + B)
          ≤ M.wrap_const + (M.wrap_left * Sval + M.wrap_right * (A + B)) := by
            exact Nat.le_add_left _ _
      _ = M.wrap_const + M.wrap_left * Sval + M.wrap_right * (A + B) := by
        simp [Nat.add_assoc]
  have hge :
      A + T ≤ M.wrap_const + M.wrap_left * Sval + M.wrap_right * (A + B) := by
    exact le_trans h_rhs_to_aS <|
      le_trans h_aS_to_aWS <|
      le_trans h_aWS_to_sum <|
      le_trans h_sum_to_wsum h_with_const
  exact Nat.not_lt_of_ge hge hspec'

/-- A positive successor pump is enough to trigger the affine barrier. -/
theorem no_affine_orients_dup_step_of_succ_pump
    {S : StepDuplicatingSchema} (M : AffineMeasure S)
    (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  apply no_affine_orients_dup_step_of_unbounded (M := M)
  intro k
  refine ⟨succIter S k, ?_⟩
  simpa using eval_succIter_ge M h_succ_bias h_succ_scale k

/-- A positive wrap/base drift is enough to trigger the affine barrier. -/
theorem no_affine_orients_dup_step_of_wrap_pump
    {S : StepDuplicatingSchema} (M : AffineMeasure S)
    (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base) :
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) := by
  apply no_affine_orients_dup_step_of_unbounded (M := M)
  intro k
  refine ⟨wrapIter S k, ?_⟩
  simpa using eval_wrapIter_ge_affine M h_wrap_bias k

/-- Abstract compositional measures on a step-duplicating schema. -/
structure CompositionalMeasure (S : StepDuplicatingSchema) where
  eval : S.T → Nat
  c_base : Nat
  c_succ : Nat → Nat
  c_wrap : Nat → Nat → Nat
  c_recur : Nat → Nat → Nat → Nat
  eval_base : eval S.base = c_base
  eval_succ : ∀ t, eval (S.succ t) = c_succ (eval t)
  eval_wrap : ∀ x y, eval (S.wrap x y) = c_wrap (eval x) (eval y)
  eval_recur : ∀ b s n, eval (S.recur b s n) = c_recur (eval b) (eval s) (eval n)
  wrap_subterm1 : ∀ x y, c_wrap x y > x
  wrap_subterm2 : ∀ x y, c_wrap x y > y

/-- Schema-level Tier 2 impossibility under base-level successor transparency. -/
theorem no_compositional_orients_dup_step_transparent_succ
    {S : StepDuplicatingSchema} (CM : CompositionalMeasure S)
    (h_transparent : CM.c_succ CM.c_base = CM.c_base) :
    ¬ (∀ (b s n : S.T),
      CM.eval (S.wrap s (S.recur b s n)) < CM.eval (S.recur b s (S.succ n))) := by
  intro h
  have hspec := h S.base S.base S.base
  simp [CM.eval_base, CM.eval_succ, CM.eval_wrap, CM.eval_recur, h_transparent] at hspec
  have hsub := CM.wrap_subterm2 CM.c_base (CM.c_recur CM.c_base CM.c_base CM.c_base)
  omega

/-- A rewrite system whose signature contains the generic duplicating step. -/
structure StepDuplicatingSystem extends StepDuplicatingSchema where
  Step : T → T → Prop
  dup_step : ∀ b s n, Step (recur b s (succ n)) (wrap s (recur b s n))

/-- A measure/order pair globally orients every step of the system. -/
def GlobalOrients {α : Type} (Sys : StepDuplicatingSystem) (m : Sys.T → α)
    (lt : α → α → Prop) : Prop :=
  ∀ {a b : Sys.T}, Sys.Step a b → lt (m b) (m a)

/-- Any additive measure on a system containing the duplicating step fails globally. -/
theorem no_global_orients_additive {Sys : StepDuplicatingSystem}
    (M : AdditiveMeasure Sys.toStepDuplicatingSchema) :
    ¬ GlobalOrients Sys M.eval (· < ·) := by
  intro h
  exact
    no_additive_orients_dup_step (S := Sys.toStepDuplicatingSchema) M
      (fun b s n => h (Sys.dup_step b s n))

/-- Any compositional measure with transparent successor at base fails globally. -/
theorem no_global_orients_compositional_transparent_succ
    {Sys : StepDuplicatingSystem} (CM : CompositionalMeasure Sys.toStepDuplicatingSchema)
    (h_transparent : CM.c_succ CM.c_base = CM.c_base) :
    ¬ GlobalOrients Sys CM.eval (· < ·) := by
  intro h
  exact
    no_compositional_orients_dup_step_transparent_succ
      (S := Sys.toStepDuplicatingSchema) CM h_transparent
      (fun b s n => h (Sys.dup_step b s n))

/-- Any globally oriented system containing the duplicating step would orient that step. -/
theorem no_global_orients_affine_of_unbounded
    {Sys : StepDuplicatingSystem} (M : AffineMeasure Sys.toStepDuplicatingSchema)
    (hunbounded : HasUnboundedRange M) :
    ¬ GlobalOrients Sys M.eval (· < ·) := by
  intro h
  exact
    no_affine_orients_dup_step_of_unbounded
      (S := Sys.toStepDuplicatingSchema) M hunbounded
      (fun b s n => h (Sys.dup_step b s n))

/-- Positive successor drift yields the affine global barrier. -/
theorem no_global_orients_affine_of_succ_pump
    {Sys : StepDuplicatingSystem} (M : AffineMeasure Sys.toStepDuplicatingSchema)
    (h_succ_bias : 1 ≤ M.succ_bias) (h_succ_scale : 1 ≤ M.succ_scale) :
    ¬ GlobalOrients Sys M.eval (· < ·) := by
  apply no_global_orients_affine_of_unbounded (M := M)
  intro k
  refine ⟨succIter Sys.toStepDuplicatingSchema k, ?_⟩
  simpa using eval_succIter_ge M h_succ_bias h_succ_scale k

/-- Positive wrap/base drift yields the affine global barrier. -/
theorem no_global_orients_affine_of_wrap_pump
    {Sys : StepDuplicatingSystem} (M : AffineMeasure Sys.toStepDuplicatingSchema)
    (h_wrap_bias : 1 ≤ M.wrap_const + M.wrap_right * M.c_base) :
    ¬ GlobalOrients Sys M.eval (· < ·) := by
  apply no_global_orients_affine_of_unbounded (M := M)
  intro k
  refine ⟨wrapIter Sys.toStepDuplicatingSchema k, ?_⟩
  simpa using eval_wrapIter_ge_affine M h_wrap_bias k

/-- Any Nat-valued global orienter is not representable by an additive measure
from the schema barrier class. -/
theorem global_orienter_not_additive_representable
    {Sys : StepDuplicatingSystem} (μ : Sys.T → Nat)
    (horient : GlobalOrients Sys μ (· < ·)) :
    ¬ ∃ M : AdditiveMeasure Sys.toStepDuplicatingSchema, M.eval = μ := by
  intro hrep
  rcases hrep with ⟨M, hM⟩
  subst hM
  exact (no_global_orients_additive (Sys := Sys) M) horient

/-- Any Nat-valued global orienter is not representable by a transparent Tier-2
compositional measure from the schema barrier class. -/
theorem global_orienter_not_compositional_transparent_representable
    {Sys : StepDuplicatingSystem} (μ : Sys.T → Nat)
    (horient : GlobalOrients Sys μ (· < ·)) :
    ¬ ∃ CM : CompositionalMeasure Sys.toStepDuplicatingSchema,
        CM.c_succ CM.c_base = CM.c_base ∧ CM.eval = μ := by
  intro hrep
  rcases hrep with ⟨CM, htrans, hCM⟩
  subst hCM
  exact (no_global_orients_compositional_transparent_succ
    (Sys := Sys) CM htrans) horient

/-- Any Nat-valued global orienter is not representable by an affine measure
from the schema barrier class when the affine measure satisfies the unbounded
pump hypothesis used by the affine theorem. -/
theorem global_orienter_not_affine_unbounded_representable
    {Sys : StepDuplicatingSystem} (μ : Sys.T → Nat)
    (horient : GlobalOrients Sys μ (· < ·)) :
    ¬ ∃ M : AffineMeasure Sys.toStepDuplicatingSchema,
        HasUnboundedRange M ∧ M.eval = μ := by
  intro hrep
  rcases hrep with ⟨M, hunbounded, hM⟩
  subst hM
  exact (no_global_orients_affine_of_unbounded
    (Sys := Sys) M hunbounded) horient

/-- Projection-style ranks that only track successor depth through the recursor argument. -/
structure ProjectionRank (S : StepDuplicatingSchema) where
  rank : S.T → Nat
  rank_base : rank S.base = 0
  rank_succ : ∀ t, rank (S.succ t) = rank t + 1
  rank_wrap : ∀ x y, rank (S.wrap x y) = 0
  rank_recur : ∀ b s n, rank (S.recur b s n) = rank n

/-- Extensionality for projection ranks by their rank functions. This is useful
    once multiple independently derived confession routes are shown to induce
    the same pointwise rank on a concrete schema. -/
@[ext] theorem ProjectionRank.ext {S : StepDuplicatingSchema}
    (R₁ R₂ : ProjectionRank S) (h : R₁.rank = R₂.rank) : R₁ = R₂ := by
  cases R₁
  cases R₂
  cases h
  simp

/-- Pointwise extensionality for projection ranks. -/
theorem ProjectionRank.ext_rank {S : StepDuplicatingSchema}
    (R₁ R₂ : ProjectionRank S)
    (h : ∀ t : S.T, R₁.rank t = R₂.rank t) : R₁ = R₂ := by
  apply ProjectionRank.ext
  funext t
  exact h t

/-- A method-agnostic witness for the confession core on a step-duplicating
schema. This is intentionally close to `ProjectionRank`: it exists as a readable
intermediate object for route-local derivations before one packages the result
as the shared projection core. -/
structure ConfessionCoreWitness (S : StepDuplicatingSchema) where
  rank : S.T → Nat
  rank_base : rank S.base = 0
  rank_succ : ∀ t, rank (S.succ t) = rank t + 1
  rank_wrap : ∀ x y, rank (S.wrap x y) = 0
  rank_recur : ∀ b s n, rank (S.recur b s n) = rank n

/-- Extensionality for confession-core witnesses by their rank functions. -/
@[ext] theorem ConfessionCoreWitness.ext {S : StepDuplicatingSchema}
    (W₁ W₂ : ConfessionCoreWitness S) (h : W₁.rank = W₂.rank) : W₁ = W₂ := by
  cases W₁
  cases W₂
  cases h
  simp

/-- Pointwise extensionality for confession-core witnesses. -/
theorem ConfessionCoreWitness.ext_rank {S : StepDuplicatingSchema}
    (W₁ W₂ : ConfessionCoreWitness S)
    (h : ∀ t : S.T, W₁.rank t = W₂.rank t) : W₁ = W₂ := by
  apply ConfessionCoreWitness.ext
  funext t
  exact h t

/-- Semantic predicates for the confession-core shape. -/
def NormalizedAtBase (S : StepDuplicatingSchema) (rank : S.T → Nat) : Prop :=
  rank S.base = 0

def TracksSuccessorDepth (S : StepDuplicatingSchema) (rank : S.T → Nat) : Prop :=
  ∀ t, rank (S.succ t) = rank t + 1

def ForgetsWrapperPayload (S : StepDuplicatingSchema) (rank : S.T → Nat) : Prop :=
  ∀ x y, rank (S.wrap x y) = 0

def FollowsRecursiveCounter (S : StepDuplicatingSchema) (rank : S.T → Nat) : Prop :=
  ∀ b s n, rank (S.recur b s n) = rank n

/-- A step-duplicating schema whose carrier is generated by the four primitive
    constructors. This is the schema-level generatedness / initiality premise
    needed to turn the confession-core semantic profile into a uniqueness
    theorem rather than only a reusable rank recipe. -/
structure GeneratedByConstructors (S : StepDuplicatingSchema) where
  generated :
    ∀ {P : S.T → Prop},
      P S.base →
      (∀ t, P t → P (S.succ t)) →
      (∀ x y, P x → P y → P (S.wrap x y)) →
      (∀ b s n, P b → P s → P n → P (S.recur b s n)) →
      ∀ t, P t

/-- On a schema generated by the primitive constructors, the confession-core
    semantic profile determines the rank function uniquely. -/
theorem semanticProfile_unique_of_generated {S : StepDuplicatingSchema}
    (G : GeneratedByConstructors S)
    {rank₁ rank₂ : S.T → Nat}
    (h1base : NormalizedAtBase S rank₁)
    (h1succ : TracksSuccessorDepth S rank₁)
    (h1wrap : ForgetsWrapperPayload S rank₁)
    (h1recur : FollowsRecursiveCounter S rank₁)
    (h2base : NormalizedAtBase S rank₂)
    (h2succ : TracksSuccessorDepth S rank₂)
    (h2wrap : ForgetsWrapperPayload S rank₂)
    (h2recur : FollowsRecursiveCounter S rank₂) :
    rank₁ = rank₂ := by
  funext t
  let P : S.T → Prop := fun u => rank₁ u = rank₂ u
  have hbaseP : P S.base := by
    dsimp [P, NormalizedAtBase] at *
    simp [h1base, h2base]
  have hsuccP : ∀ u, P u → P (S.succ u) := by
    intro u hu
    dsimp [P] at hu ⊢
    rw [h1succ, h2succ, hu]
  have hwrapP : ∀ x y, P x → P y → P (S.wrap x y) := by
    intro x y _ _
    dsimp [P] at ⊢
    rw [h1wrap, h2wrap]
  have hrecurP : ∀ b s n, P b → P s → P n → P (S.recur b s n) := by
    intro b s n _ _ hn
    dsimp [P] at hn ⊢
    rw [h1recur, h2recur, hn]
  exact G.generated hbaseP hsuccP hwrapP hrecurP t

namespace ConfessionCoreWitness

/-- Build a confession-core witness from the semantic profile predicates. -/
def ofSemanticProfile {S : StepDuplicatingSchema} (rank : S.T → Nat)
    (hbase : NormalizedAtBase S rank)
    (hsucc : TracksSuccessorDepth S rank)
    (hwrap : ForgetsWrapperPayload S rank)
    (hrecur : FollowsRecursiveCounter S rank) : ConfessionCoreWitness S where
  rank := rank
  rank_base := hbase
  rank_succ := hsucc
  rank_wrap := hwrap
  rank_recur := hrecur

/-- Every confession-core witness satisfies the semantic profile predicates. -/
theorem satisfies_semantic_profile {S : StepDuplicatingSchema}
    (W : ConfessionCoreWitness S) :
    NormalizedAtBase S W.rank
    ∧ TracksSuccessorDepth S W.rank
    ∧ ForgetsWrapperPayload S W.rank
    ∧ FollowsRecursiveCounter S W.rank := by
  exact ⟨W.rank_base, W.rank_succ, W.rank_wrap, W.rank_recur⟩

end ConfessionCoreWitness

/-- Generic route-evidence adapter layer above concrete method-specific witness
    records. A `RouteEvidence S` packages only the schema-semantic profile that
    a concrete route has established, without committing to any particular
    route-specific witness vocabulary. -/
structure RouteEvidence (S : StepDuplicatingSchema) where
  rank : S.T → Nat
  rank_base : rank S.base = 0
  rank_succ : ∀ t, rank (S.succ t) = rank t + 1
  rank_wrap : ∀ x y, rank (S.wrap x y) = 0
  rank_recur : ∀ b s n, rank (S.recur b s n) = rank n

namespace RouteEvidence

/-- Every route-evidence object packages to the shared confession core. -/
def toConfessionCoreWitness {S : StepDuplicatingSchema}
    (E : RouteEvidence S) : ConfessionCoreWitness S where
  rank := E.rank
  rank_base := E.rank_base
  rank_succ := E.rank_succ
  rank_wrap := E.rank_wrap
  rank_recur := E.rank_recur

/-- Every route-evidence object packages to the corresponding projection rank. -/
def toProjectionRank {S : StepDuplicatingSchema}
    (E : RouteEvidence S) : ProjectionRank S where
  rank := E.rank
  rank_base := E.rank_base
  rank_succ := E.rank_succ
  rank_wrap := E.rank_wrap
  rank_recur := E.rank_recur

/-- Any confession-core witness can be viewed as generic route evidence. -/
def ofConfessionCoreWitness {S : StepDuplicatingSchema}
    (W : ConfessionCoreWitness S) : RouteEvidence S where
  rank := W.rank
  rank_base := W.rank_base
  rank_succ := W.rank_succ
  rank_wrap := W.rank_wrap
  rank_recur := W.rank_recur

/-- Any projection rank can be viewed as generic route evidence. -/
def ofProjectionRank {S : StepDuplicatingSchema}
    (R : ProjectionRank S) : RouteEvidence S where
  rank := R.rank
  rank_base := R.rank_base
  rank_succ := R.rank_succ
  rank_wrap := R.rank_wrap
  rank_recur := R.rank_recur

@[simp] theorem toConfessionCoreWitness_rank {S : StepDuplicatingSchema}
    (E : RouteEvidence S) :
    E.toConfessionCoreWitness.rank = E.rank := rfl

@[simp] theorem toProjectionRank_rank {S : StepDuplicatingSchema}
    (E : RouteEvidence S) :
    E.toProjectionRank.rank = E.rank := rfl

@[simp] theorem ofConfessionCoreWitness_rank {S : StepDuplicatingSchema}
    (W : ConfessionCoreWitness S) :
    (ofConfessionCoreWitness W).rank = W.rank := rfl

@[simp] theorem ofProjectionRank_rank {S : StepDuplicatingSchema}
    (R : ProjectionRank S) :
    (ofProjectionRank R).rank = R.rank := rfl

@[ext] theorem ext_rank {S : StepDuplicatingSchema}
    (E₁ E₂ : RouteEvidence S)
    (h : ∀ t, E₁.rank t = E₂.rank t) : E₁ = E₂ := by
  have hr : E₁.rank = E₂.rank := funext h
  cases E₁
  cases E₂
  cases hr
  simp

theorem satisfies_semantic_profile {S : StepDuplicatingSchema}
    (E : RouteEvidence S) :
    NormalizedAtBase S E.rank
    ∧ TracksSuccessorDepth S E.rank
    ∧ ForgetsWrapperPayload S E.rank
    ∧ FollowsRecursiveCounter S E.rank := by
  exact ⟨E.rank_base, E.rank_succ, E.rank_wrap, E.rank_recur⟩

end RouteEvidence

/-- The projection rank orients the duplicating step by tracking only the recursion counter. -/
theorem projection_orients_dup_step {S : StepDuplicatingSchema} (R : ProjectionRank S)
    (b s n : S.T) :
    R.rank (S.wrap s (S.recur b s n)) < R.rank (S.recur b s (S.succ n)) := by
  rw [R.rank_wrap, R.rank_recur, R.rank_succ]
  omega

/-- The projection rank violates sensitivity to the first wrapper argument. -/
theorem projection_violates_wrap_subterm1 {S : StepDuplicatingSchema} (R : ProjectionRank S) :
    ∃ x y : S.T, ¬ (R.rank (S.wrap x y) > R.rank x) := by
  refine ⟨S.succ S.base, S.base, ?_⟩
  rw [R.rank_wrap, R.rank_succ, R.rank_base]
  omega

/-- The projection rank violates sensitivity to the second wrapper argument. -/
theorem projection_violates_wrap_subterm2 {S : StepDuplicatingSchema} (R : ProjectionRank S) :
    ∃ x y : S.T, ¬ (R.rank (S.wrap x y) > R.rank y) := by
  refine ⟨S.base, S.succ S.base, ?_⟩
  rw [R.rank_wrap, R.rank_succ, R.rank_base]
  omega

/-- Any rank satisfying the semantic confession-core profile orients the
    duplicating step. -/
theorem semanticProfile_orients_dup_step {S : StepDuplicatingSchema}
    {rank : S.T → Nat}
    (_hbase : NormalizedAtBase S rank)
    (hsucc : TracksSuccessorDepth S rank)
    (hwrap : ForgetsWrapperPayload S rank)
    (hrecur : FollowsRecursiveCounter S rank)
    (b s n : S.T) :
    rank (S.wrap s (S.recur b s n)) < rank (S.recur b s (S.succ n)) := by
  rw [hwrap, hrecur, hsucc]
  omega

/-- Any rank satisfying the semantic confession-core profile violates wrapper
    sensitivity on the first payload coordinate. -/
theorem semanticProfile_violates_wrap_subterm1 {S : StepDuplicatingSchema}
    {rank : S.T → Nat}
    (hbase : NormalizedAtBase S rank)
    (hsucc : TracksSuccessorDepth S rank)
    (hwrap : ForgetsWrapperPayload S rank) :
    ∃ x y : S.T, ¬ (rank (S.wrap x y) > rank x) := by
  refine ⟨S.succ S.base, S.base, ?_⟩
  rw [hwrap, hsucc, hbase]
  omega

/-- Any rank satisfying the semantic confession-core profile violates wrapper
    sensitivity on the second payload coordinate. -/
theorem semanticProfile_violates_wrap_subterm2 {S : StepDuplicatingSchema}
    {rank : S.T → Nat}
    (hbase : NormalizedAtBase S rank)
    (hsucc : TracksSuccessorDepth S rank)
    (hwrap : ForgetsWrapperPayload S rank) :
    ∃ x y : S.T, ¬ (rank (S.wrap x y) > rank y) := by
  refine ⟨S.base, S.succ S.base, ?_⟩
  rw [hwrap, hsucc, hbase]
  omega

namespace ConfessionCoreWitness

/-- Package a confession-core witness as the shared projection core. -/
def toProjectionRank {S : StepDuplicatingSchema}
    (W : ConfessionCoreWitness S) : ProjectionRank S where
  rank := W.rank
  rank_base := W.rank_base
  rank_succ := W.rank_succ
  rank_wrap := W.rank_wrap
  rank_recur := W.rank_recur

/-- Every projection rank already furnishes a confession-core witness. -/
def ofProjectionRank {S : StepDuplicatingSchema}
    (R : ProjectionRank S) : ConfessionCoreWitness S where
  rank := R.rank
  rank_base := R.rank_base
  rank_succ := R.rank_succ
  rank_wrap := R.rank_wrap
  rank_recur := R.rank_recur

@[simp] theorem toProjectionRank_rank {S : StepDuplicatingSchema}
    (W : ConfessionCoreWitness S) :
    W.toProjectionRank.rank = W.rank := rfl

@[simp] theorem ofProjectionRank_rank {S : StepDuplicatingSchema}
    (R : ProjectionRank S) :
    (ofProjectionRank R).rank = R.rank := rfl

@[simp] theorem ofProjectionRank_toProjectionRank {S : StepDuplicatingSchema}
    (R : ProjectionRank S) :
    (ofProjectionRank R).toProjectionRank = R := by
  rfl

@[simp] theorem toProjectionRank_ofProjectionRank {S : StepDuplicatingSchema}
    (W : ConfessionCoreWitness S) :
    ofProjectionRank W.toProjectionRank = W := by
  cases W
  rfl

/-- On a generated schema, any two confession-core witnesses are equal. -/
theorem unique_of_generated {S : StepDuplicatingSchema}
    (G : GeneratedByConstructors S)
    (W₁ W₂ : ConfessionCoreWitness S) :
    W₁ = W₂ := by
  apply ConfessionCoreWitness.ext_rank
  intro t
  exact congrFun
    (semanticProfile_unique_of_generated G
      W₁.rank_base W₁.rank_succ W₁.rank_wrap W₁.rank_recur
      W₂.rank_base W₂.rank_succ W₂.rank_wrap W₂.rank_recur) t

end ConfessionCoreWitness

/-- On a generated schema, any two projection ranks are equal. -/
theorem projectionRank_unique_of_generated {S : StepDuplicatingSchema}
    (G : GeneratedByConstructors S)
    (R₁ R₂ : ProjectionRank S) :
    R₁ = R₂ := by
  apply ProjectionRank.ext_rank
  intro t
  exact congrFun
    (semanticProfile_unique_of_generated G
      R₁.rank_base R₁.rank_succ R₁.rank_wrap R₁.rank_recur
      R₂.rank_base R₂.rank_succ R₂.rank_wrap R₂.rank_recur) t

end StepDuplicatingSchema
end OperatorKO7.StepDuplicating
