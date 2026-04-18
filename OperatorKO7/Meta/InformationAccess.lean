import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Information Access, Sequentiality, and Terminal Record

Finite-discrete mechanization of Paper 2 Section 2.

This file formalizes two layers.

1. A generic access-based notion of meta/object interaction:
   - non-vacuous query,
   - direct retrieval,
   - sequential uncertainty reduction,
   - hidden-progress necessity.
2. A concrete primitive-duplicator progress model:
   - hidden progress coordinate entropy,
   - exact recovery channels,
   - terminal-record persistence,
   - retrospective recovery of the progress index.

The Shannon-side formulas here are the exact finite/uniform ones needed by the
paper; they do not rely on a full probability-theory entropy stack.
-/

namespace OperatorKO7.InformationAccess

open scoped Real

/-! ## Generic access-based layer -/

/-- `target` is directly accessible from `obs` when some decoder recovers it
from the observable state alone. -/
def AccessibleFrom {α β γ : Type} (obs : α → β) (target : α → γ) : Prop :=
  ∃ decode : β → γ, target = decode ∘ obs

/-- Generic meta/object access model. -/
structure MetaAccessModel (α M V T : Type) where
  metaView : α → M
  verdict : α → V
  trace : Nat → α → T

namespace MetaAccessModel

variable {α M V T : Type}

/-- The initial access point available to the meta layer. -/
def initialAccess (A : MetaAccessModel α M V T) : α → M × T :=
  fun x => (A.metaView x, A.trace 0 x)

/-- The stage-`k` access point available after sequential object computation. -/
def stageAccess (A : MetaAccessModel α M V T) (k : Nat) : α → M × T :=
  fun x => (A.metaView x, A.trace k x)

/-- A query is non-vacuous if the verdict is not already meta-accessible. -/
def NonvacuousMetaQuery (A : MetaAccessModel α M V T) : Prop :=
  ¬ AccessibleFrom A.metaView A.verdict

/-- Direct retrieval means the verdict is already available at the initial
access point. -/
def DirectRetrieval (A : MetaAccessModel α M V T) : Prop :=
  AccessibleFrom A.initialAccess A.verdict

/-- Sequential uncertainty reduction means the verdict is not directly
retrievable at the initial access point, but becomes retrievable at a later
stage. -/
def SequentialUncertaintyReduction
    (A : MetaAccessModel α M V T) (k : Nat) : Prop :=
  ¬ A.DirectRetrieval ∧ AccessibleFrom (A.stageAccess k) A.verdict

/-- Paper 2 Proposition 2.3 / 2.12: a non-vacuous query means the verdict is
not yet accessible to the meta layer. -/
theorem information_seeking_character_of_nonvacuous_query
    (A : MetaAccessModel α M V T) :
    A.NonvacuousMetaQuery ↔ ¬ AccessibleFrom A.metaView A.verdict := by
  rfl

/-- If the verdict is meta-accessible already, then it is also directly
retrievable at the initial access point by ignoring the object component. -/
theorem meta_accessible_implies_directRetrieval
    (A : MetaAccessModel α M V T)
    (hmeta : AccessibleFrom A.metaView A.verdict) :
    A.DirectRetrieval := by
  rcases hmeta with ⟨decode, hdecode⟩
  refine ⟨fun mt => decode mt.1, ?_⟩
  funext x
  simp [initialAccess, hdecode, Function.comp]

/-- Direct retrieval is incompatible with sequential uncertainty reduction. -/
theorem directRetrieval_not_sequential_resolution
    (A : MetaAccessModel α M V T) (k : Nat) :
    A.DirectRetrieval → ¬ A.SequentialUncertaintyReduction k := by
  intro hdirect hseq
  exact hseq.1 hdirect

/-- Any sequential resolver is automatically non-vacuous at the pure meta
layer: otherwise the verdict would already be directly retrievable. -/
theorem sequential_resolution_implies_nonvacuous
    (A : MetaAccessModel α M V T) {k : Nat}
    (hseq : A.SequentialUncertaintyReduction k) :
    A.NonvacuousMetaQuery := by
  intro hmeta
  exact hseq.1 (A.meta_accessible_implies_directRetrieval hmeta)

/-- If the terminal trace state were itself meta-accessible, then the verdict
would already be directly retrievable. Hence sequential resolution forces the
terminal trace state to remain hidden from the meta layer alone. -/
theorem sequential_resolution_requires_hidden_terminal_state
    (A : MetaAccessModel α M V T) {k : Nat}
    (hseq : A.SequentialUncertaintyReduction k) :
    ¬ AccessibleFrom A.metaView (A.trace k) := by
  intro hterminal
  rcases hterminal with ⟨lift, hlift⟩
  rcases hseq.2 with ⟨decode, hdecode⟩
  have hmeta : AccessibleFrom A.metaView A.verdict := by
    refine ⟨fun m => decode (m, lift m), ?_⟩
    funext x
    simp [stageAccess, hlift, hdecode, Function.comp]
  exact hseq.1 (A.meta_accessible_implies_directRetrieval hmeta)

/-- Paper 2 Proposition 2.5 / 2.14: sequential resolution yields an explicitly
hidden verdict-relevant statistic. We may take the terminal trace state itself
as that statistic. -/
theorem sequential_resolution_requires_hidden_state
    (A : MetaAccessModel α M V T) {k : Nat}
    (hseq : A.SequentialUncertaintyReduction k) :
    ∃ φ : α → T,
      ¬ AccessibleFrom A.metaView φ
        ∧ AccessibleFrom (fun x => (A.metaView x, φ x)) A.verdict := by
  refine ⟨A.trace k, A.sequential_resolution_requires_hidden_terminal_state hseq, ?_⟩
  simpa using hseq.2

end MetaAccessModel

/-! ## Progress coordinate and channel costs -/

/-- Uniform Shannon entropy in bits of the progress coordinate
`j ∈ {0, ..., K}`. -/
noncomputable def progressEntropyBits (K : Nat) : ℝ :=
  Real.logb 2 (K + 1 : ℝ)

/-- Minimal exact binary code length for `K + 1` possibilities. -/
def optimalRecoveryBits (K : Nat) : Nat :=
  Nat.clog 2 (K + 1)

/-- History observation cost model: storing the full prefix of `j + 1`
progress-bearing states with per-state payload width `atomWidth`. -/
def historyObservationBitCost (atomWidth j : Nat) : Nat :=
  atomWidth * ((j + 1) * (j + 2) / 2)

/-- Structural counting uses only the exact progress index. -/
def structuralCountingBitCost (K : Nat) : Nat :=
  optimalRecoveryBits K

/-- Origin comparison also uses only the exact progress index. -/
def originComparisonBitCost (K : Nat) : Nat :=
  optimalRecoveryBits K

/-- Parallel clocking likewise uses only the exact progress index. -/
def parallelClockBitCost (K : Nat) : Nat :=
  optimalRecoveryBits K

@[simp] theorem progress_entropy_uniform (K : Nat) :
    progressEntropyBits K = Real.logb 2 (K + 1 : ℝ) := rfl

@[simp] theorem structural_counting_optimal (K : Nat) :
    structuralCountingBitCost K = optimalRecoveryBits K := rfl

@[simp] theorem origin_comparison_optimal (K : Nat) :
    originComparisonBitCost K = optimalRecoveryBits K := rfl

@[simp] theorem parallel_clocking_optimal (K : Nat) :
    parallelClockBitCost K = optimalRecoveryBits K := rfl

/-- Terminal history-observation cost is quadratic in the trace length in the
explicit prefix-storage model. -/
@[simp] theorem history_observation_terminal_cost (atomWidth K : Nat) :
    historyObservationBitCost atomWidth K =
      atomWidth * ((K + 1) * (K + 2) / 2) := rfl

/-- For positive payload width, the history-observation channel incurs at least
quadratic-over-linear growth in the terminal trace length. -/
theorem history_observation_quadratic_overcost
    (atomWidth K : Nat) (hwidth : 1 ≤ atomWidth) :
    (K * (K + 1)) / 2 ≤ historyObservationBitCost atomWidth K := by
  unfold historyObservationBitCost
  have hquad :
      (K * (K + 1)) / 2 ≤ ((K + 1) * (K + 2)) / 2 := by
    apply Nat.div_le_div_right
    nlinarith [Nat.zero_le K]
  have hscale :
      ((K + 1) * (K + 2)) / 2 ≤
        (((K + 1) * (K + 2)) / 2) * atomWidth := by
    simpa using Nat.mul_le_mul_left (((K + 1) * (K + 2)) / 2) hwidth
  calc
    (K * (K + 1)) / 2 ≤ ((K + 1) * (K + 2)) / 2 := hquad
    _ ≤ (((K + 1) * (K + 2)) / 2) * atomWidth := hscale
    _ = atomWidth * (((K + 1) * (K + 2)) / 2) := by ring

/-! ## Primitive duplicator syntax and terminal record -/

/-- Minimal syntax for the primitive self-duplicating recursor of Paper 2. -/
inductive PrimitiveDuplicatorTerm
  | seedX
  | seedY
  | zero
  | succ : PrimitiveDuplicatorTerm → PrimitiveDuplicatorTerm
  | g : PrimitiveDuplicatorTerm → PrimitiveDuplicatorTerm → PrimitiveDuplicatorTerm
  | f : PrimitiveDuplicatorTerm → PrimitiveDuplicatorTerm → PrimitiveDuplicatorTerm → PrimitiveDuplicatorTerm
  deriving DecidableEq, Repr

namespace PrimitiveDuplicatorTerm

/-- Counter `S^K(0)`. -/
def counter : Nat → PrimitiveDuplicatorTerm
  | 0 => .zero
  | n + 1 => .succ (counter n)

/-- Left-nested `G`-stack `G^i(Y, t)`. -/
def gChain : Nat → PrimitiveDuplicatorTerm → PrimitiveDuplicatorTerm
  | 0, t => t
  | n + 1, t => .g .seedY (gChain n t)

/-- Canonical nonterminal stage
`G^i(Y, F(X,Y,S^{K-i}(0)))`. -/
def stage (K i : Nat) : PrimitiveDuplicatorTerm :=
  gChain i (.f .seedX .seedY (counter (K - i)))

/-- Terminal record map `R_K(X,Y) = G^K(Y,X)`. -/
def terminalRecordMap (K : Nat) : PrimitiveDuplicatorTerm :=
  gChain K .seedX

/-- Count active `F`-sites. -/
def activeFCount : PrimitiveDuplicatorTerm → Nat
  | .seedX => 0
  | .seedY => 0
  | .zero => 0
  | .succ t => activeFCount t
  | .g x y => activeFCount x + activeFCount y
  | .f x y z => activeFCount x + activeFCount y + activeFCount z + 1

/-- Count visible `G`-frames. -/
def gFrameCount : PrimitiveDuplicatorTerm → Nat
  | .seedX => 0
  | .seedY => 0
  | .zero => 0
  | .succ t => gFrameCount t
  | .g x y => gFrameCount x + gFrameCount y + 1
  | .f x y z => gFrameCount x + gFrameCount y + gFrameCount z

@[simp] theorem counter_zero : counter 0 = .zero := rfl

@[simp] theorem counter_succ (n : Nat) : counter (n + 1) = .succ (counter n) := rfl

@[simp] theorem activeFCount_counter (K : Nat) : activeFCount (counter K) = 0 := by
  induction K with
  | zero => rfl
  | succ K ih => simpa [counter, activeFCount] using ih

@[simp] theorem gFrameCount_counter (K : Nat) : gFrameCount (counter K) = 0 := by
  induction K with
  | zero => rfl
  | succ K ih => simpa [counter, gFrameCount] using ih

@[simp] theorem activeFCount_gChain (i : Nat) (t : PrimitiveDuplicatorTerm) :
    activeFCount (gChain i t) = activeFCount t := by
  induction i with
  | zero => rfl
  | succ i ih =>
      simp [gChain, activeFCount, ih]

@[simp] theorem gFrameCount_gChain (i : Nat) (t : PrimitiveDuplicatorTerm) :
    gFrameCount (gChain i t) = i + gFrameCount t := by
  induction i with
  | zero => simp [gChain]
  | succ i ih =>
      simp [gChain, gFrameCount, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Along every nonterminal canonical stage there is exactly one active `F`-site. -/
theorem live_computation_channel_unique (K i : Nat) :
    activeFCount (stage K i) = 1 := by
  simp [stage, activeFCount_gChain, activeFCount_counter, activeFCount]

/-- The visible multiplicity of `G`-frames along the canonical stage is exactly
its progress index. -/
theorem visible_record_multiplicity (K i : Nat) :
    gFrameCount (stage K i) = i := by
  simp [stage, gFrameCount_gChain, gFrameCount_counter, gFrameCount]

/-- The terminal record contains no active `F`-site. -/
theorem terminal_record_has_no_live_site (K : Nat) :
    activeFCount (terminalRecordMap K) = 0 := by
  rw [terminalRecordMap, activeFCount_gChain, activeFCount]

/-- The terminal record retains exact depth via `G`-multiplicity. -/
theorem terminal_record_recovers_progress_exactly (K : Nat) :
    gFrameCount (terminalRecordMap K) = K := by
  rw [terminalRecordMap, gFrameCount_gChain, gFrameCount, Nat.add_zero]

/-- Paper 2 Proposition 2.10 / 2.18: live computation versus terminal record
for the primitive duplicator. -/
theorem live_computation_vs_terminal_record (K i : Nat) :
    activeFCount (stage K i) = 1
      ∧ gFrameCount (stage K i) = i
      ∧ activeFCount (terminalRecordMap K) = 0
      ∧ gFrameCount (terminalRecordMap K) = K := by
  exact ⟨live_computation_channel_unique K i,
    visible_record_multiplicity K i,
    terminal_record_has_no_live_site K,
    terminal_record_recovers_progress_exactly K⟩

end PrimitiveDuplicatorTerm

/-! ## Exact-recovery channels for the hidden progress coordinate -/

/-- Structural counting recovers the progress coordinate exactly. -/
def structuralCountingChannel {K : Nat} : Fin (K + 1) → Fin (K + 1) :=
  fun j => j

/-- Origin comparison recovers the same coordinate exactly. -/
def originComparisonChannel {K : Nat} : Fin (K + 1) → Fin (K + 1) :=
  fun j => j

/-- Parallel clocking recovers the same coordinate exactly. -/
def parallelClockChannel {K : Nat} : Fin (K + 1) → Fin (K + 1) :=
  fun j => j

@[simp] theorem structuralCountingChannel_injective {K : Nat} :
    Function.Injective (@structuralCountingChannel K) := by
  intro a b h
  simpa using h

@[simp] theorem originComparisonChannel_injective {K : Nat} :
    Function.Injective (@originComparisonChannel K) := by
  intro a b h
  simpa using h

@[simp] theorem parallelClockChannel_injective {K : Nat} :
    Function.Injective (@parallelClockChannel K) := by
  intro a b h
  simpa using h

/-- Prior entropy for the terminal index `K ∈ {1, ..., Kmax}` under the uniform
prior used in Paper 2. -/
noncomputable def terminalPriorEntropyBits (Kmax : Nat) : ℝ :=
  Real.logb 2 (Kmax : ℝ)

/-- Posterior entropy after exact recovery from the terminal record. -/
noncomputable def terminalPosteriorEntropyBits (_Kmax : Nat) : ℝ := 0

/-- Mutual-information gain at terminal under exact recovery. -/
noncomputable def terminalMutualInformationGainBits (Kmax : Nat) : ℝ :=
  terminalPriorEntropyBits Kmax - terminalPosteriorEntropyBits Kmax

/-- Paper 2 Corollary 2.9: the terminal record recovers the progress index
exactly, so the full prior entropy is gained. -/
theorem meta_trace_mutual_information_at_terminal (Kmax : Nat) :
    terminalMutualInformationGainBits Kmax = terminalPriorEntropyBits Kmax := by
  simp [terminalMutualInformationGainBits, terminalPriorEntropyBits,
    terminalPosteriorEntropyBits]

end OperatorKO7.InformationAccess
