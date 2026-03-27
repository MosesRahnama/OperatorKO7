import OperatorKO7.Meta.MutualDuplication_PayloadFlow
import OperatorKO7.Meta.GraphPathExtraction
import OperatorKO7.Meta.FiniteGraphReachability
import OperatorKO7.Meta.FiniteGraphSCC

/-!
# Raw-Graph Preserving Packet SCC Barrier

This module lifts the synchronized preserving SCC story from finite cyclic packet systems
to an arbitrary directed graph equipped with:

- a shared wrapper and empty payload state,
- a family of graph-indexed recursors and packet constructors,
- local packet-forwarding rules along graph edges, and
- an explicit closed cycle witness in the raw graph.

As with the delayed-duplication graph theorem, the result is witness-based rather than
algorithmic. But once a concrete graph cycle with synchronized packet forwarding is
certified, the additive, affine, transparent, and scalar-projection contextual barriers
follow uniformly.
-/

namespace OperatorKO7.MutualDuplicationPacketGraph

open OperatorKO7.DependencyPairsFragment
open OperatorKO7.MutualDuplicationPayloadFlow
open OperatorKO7.GraphPathExtraction
open OperatorKO7.FiniteGraphReachability
open OperatorKO7.FiniteGraphSCC

/-- A synchronized packet system indexed by an arbitrary directed graph. -/
structure GraphPacketSystem (ι : Type) where
  T : Type
  empty : T
  wrap : T → T → T
  recur : ι → T → T → T
  packet : ι → Nat → T → T
  packet_zero : ∀ i p, packet i 0 p = empty
  Edge : ι → ι → Prop
  Step : T → T → Prop
  step_packet :
    ∀ {i j}, Edge i j → ∀ ctx payload n,
      Step (recur i ctx (packet i (n + 1) payload))
        (wrap payload (recur j ctx (packet j n payload)))

namespace GraphPacketSystem

/-- The syntax at a fixed graph node as an abstract packet model. -/
def toPacketModel {ι : Type} (Sys : GraphPacketSystem ι) (i : ι) : PacketModel Sys.T where
  empty := Sys.empty
  wrap := Sys.wrap
  recur := Sys.recur i
  packet := Sys.packet i

/-- Minimal context closure: root steps plus right-wrapper descent. -/
inductive StepCtx {ι : Type} (Sys : GraphPacketSystem ι) : Sys.T → Sys.T → Prop
| root : ∀ {a b}, Sys.Step a b → StepCtx Sys a b
| wrap_right : ∀ s {a b}, StepCtx Sys a b → StepCtx Sys (Sys.wrap s a) (Sys.wrap s b)

/-- Orientation of the induced contextual relation. -/
def GlobalOrientsCtx {ι : Type} (Sys : GraphPacketSystem ι) (m : Sys.T → Nat) : Prop :=
  ∀ {a b : Sys.T}, StepCtx Sys a b → m b < m a

/-- Generic wrapper nesting on the shared carrier. -/
def wrapNest {ι : Type} (Sys : GraphPacketSystem ι) (p : Sys.T) : Nat → Sys.T → Sys.T
  | 0, t => t
  | n + 1, t => wrapNest Sys p n (Sys.wrap p t)

namespace StepCtx

lemma wrapNest_right {ι : Type} {Sys : GraphPacketSystem ι} (p : Sys.T) :
    ∀ n {a b : Sys.T}, StepCtx Sys a b →
      StepCtx Sys (GraphPacketSystem.wrapNest Sys p n a) (GraphPacketSystem.wrapNest Sys p n b)
  | 0, _, _, h => by simpa [GraphPacketSystem.wrapNest] using h
  | n + 1, _, _, h => by
      simpa [GraphPacketSystem.wrapNest] using
        wrapNest_right p n (StepCtx.wrap_right p h)

end StepCtx

/-- A certified closed cycle in the raw graph. -/
structure CyclePath {ι : Type} (Sys : GraphPacketSystem ι) where
  copies : Nat
  hcopies : 0 < copies
  node : Nat → ι
  edge : ∀ r, r < copies → Sys.Edge (node r) (node (r + 1))
  closed : node copies = node 0

/-- Build a concrete graph cycle from any nonempty closed transitive-closure witness. -/
noncomputable def ofClosedTransGen {ι : Type} {Sys : GraphPacketSystem ι} {i : ι}
    (hcycle : Relation.TransGen Sys.Edge i i) : CyclePath Sys := by
  let P := EdgePath.ofTransGen hcycle
  refine
    { copies := P.len
      hcopies := P.hlen
      node := P.node
      edge := P.edge
      closed := ?_ }
  simpa [P.start] using P.finish

/-- Build a concrete graph cycle from a round-trip SCC witness. -/
noncomputable def ofRoundTrip {ι : Type} {Sys : GraphPacketSystem ι} {i j : ι}
    (hij : Relation.TransGen Sys.Edge i j) (hji : Relation.TransGen Sys.Edge j i) :
    CyclePath Sys := by
  let P := EdgePath.ofRoundTrip hij hji
  refine
    { copies := P.len
      hcopies := P.hlen
      node := P.node
      edge := P.edge
      closed := ?_ }
  simpa [P.start] using P.finish

@[simp] theorem ofClosedTransGen_node0 {ι : Type} {Sys : GraphPacketSystem ι} {i : ι}
    (hcycle : Relation.TransGen Sys.Edge i i) :
    (ofClosedTransGen hcycle).node 0 = i := by
  simpa [ofClosedTransGen] using (EdgePath.ofTransGen hcycle).start

@[simp] theorem ofRoundTrip_node0 {ι : Type} {Sys : GraphPacketSystem ι} {i j : ι}
    (hij : Relation.TransGen Sys.Edge i j) (hji : Relation.TransGen Sys.Edge j i) :
    (ofRoundTrip hij hji).node 0 = i := by
  simpa [ofRoundTrip] using (EdgePath.ofRoundTrip hij hji).start

namespace CyclePath

variable {ι : Type} {Sys : GraphPacketSystem ι}

/-- Uniform additive measures on the graph-indexed packet SCC syntax. -/
structure AdditiveMeasure (Sys : GraphPacketSystem ι) where
  eval : Sys.T → Nat
  w_empty : Nat
  w_wrap : Nat
  w_recur : Nat
  eval_empty : eval Sys.empty = w_empty
  eval_wrap : ∀ x y, eval (Sys.wrap x y) = w_wrap + eval x + eval y
  eval_recur : ∀ i ctx packet, eval (Sys.recur i ctx packet) = w_recur + eval ctx + eval packet
  eval_packet : ∀ i n p, eval (Sys.packet i n p) = n * eval p + w_empty
  h_wrap_pos : 1 ≤ w_wrap

/-- Uniform affine measures on the graph-indexed packet SCC syntax. -/
structure AffineMeasure (Sys : GraphPacketSystem ι) where
  eval : Sys.T → Nat
  c_empty : Nat
  wrap_const : Nat
  wrap_left : Nat
  wrap_right : Nat
  recur_const : Nat
  recur_ctx : Nat
  recur_packet : Nat
  eval_empty : eval Sys.empty = c_empty
  eval_wrap :
    ∀ x y, eval (Sys.wrap x y) = wrap_const + wrap_left * eval x + wrap_right * eval y
  eval_recur :
    ∀ i ctx packet,
      eval (Sys.recur i ctx packet) = recur_const + recur_ctx * eval ctx + recur_packet * eval packet
  eval_packet : ∀ i n p, eval (Sys.packet i n p) = n * eval p + c_empty
  h_wrap_left_pos : 1 ≤ wrap_left
  h_wrap_right_pos : 1 ≤ wrap_right

/-- Uniform transparent packet-bookkeeping measures on the graph-indexed packet SCC syntax. -/
structure TransparentMeasure (Sys : GraphPacketSystem ι) where
  eval : Sys.T → Nat
  c_empty : Nat
  c_wrap : Nat → Nat → Nat
  c_recur : Nat → Nat → Nat
  eval_empty : eval Sys.empty = c_empty
  eval_wrap : ∀ x y, eval (Sys.wrap x y) = c_wrap (eval x) (eval y)
  eval_recur : ∀ i ctx packet, eval (Sys.recur i ctx packet) = c_recur (eval ctx) (eval packet)
  eval_packet : ∀ i n p, eval (Sys.packet i n p) = c_empty
  wrap_subterm2 : ∀ x y, c_wrap x y > y

def AdditiveMeasure.toPacketModelMeasure (M : AdditiveMeasure Sys) (i : ι) :
    MutualDuplicationPayloadFlow.AdditiveMeasure (Sys.toPacketModel i) where
  eval := M.eval
  w_empty := M.w_empty
  w_wrap := M.w_wrap
  w_recur := M.w_recur
  eval_empty := M.eval_empty
  eval_wrap := M.eval_wrap
  eval_recur := M.eval_recur i
  eval_packet := M.eval_packet i
  h_wrap_pos := M.h_wrap_pos

def AffineMeasure.toPacketModelMeasure (M : AffineMeasure Sys) (i : ι) :
    MutualDuplicationPayloadFlow.AffineMeasure (Sys.toPacketModel i) where
  eval := M.eval
  c_empty := M.c_empty
  wrap_const := M.wrap_const
  wrap_left := M.wrap_left
  wrap_right := M.wrap_right
  recur_const := M.recur_const
  recur_ctx := M.recur_ctx
  recur_packet := M.recur_packet
  eval_empty := M.eval_empty
  eval_wrap := M.eval_wrap
  eval_recur := M.eval_recur i
  eval_packet := M.eval_packet i
  h_wrap_left_pos := M.h_wrap_left_pos
  h_wrap_right_pos := M.h_wrap_right_pos

def TransparentMeasure.toPacketModelMeasure (M : TransparentMeasure Sys) (i : ι) :
    MutualDuplicationPayloadFlow.TransparentMeasure (Sys.toPacketModel i) where
  eval := M.eval
  c_empty := M.c_empty
  c_wrap := M.c_wrap
  c_recur := M.c_recur
  eval_empty := M.eval_empty
  eval_wrap := M.eval_wrap
  eval_recur := M.eval_recur i
  eval_packet := M.eval_packet i
  wrap_subterm2 := M.wrap_subterm2

/-- Residual phase after `r` latent packets remain. -/
def phase (C : CyclePath Sys) (ctx payload : Sys.T) (r : Nat) : Sys.T :=
  GraphPacketSystem.wrapNest Sys payload (C.copies - r)
    (Sys.recur (C.node (C.copies - r)) ctx (Sys.packet (C.node (C.copies - r)) r payload))

lemma packetFlow_wrapNest_eq (C : CyclePath Sys) (payload : Sys.T) :
    ∀ n t,
      GraphPacketSystem.wrapNest Sys payload n t =
        MutualDuplicationPayloadFlow.wrapNest Sys.wrap payload n t
  | 0, t => by rfl
  | n + 1, t => by
      rw [GraphPacketSystem.wrapNest, MutualDuplicationPayloadFlow.wrapNest,
        packetFlow_wrapNest_eq C payload n]

lemma phase_step (C : CyclePath Sys) (ctx payload : Sys.T) {r : Nat} (hr : r < C.copies) :
    StepCtx Sys (phase C ctx payload (r + 1)) (phase C ctx payload r) := by
  let idx := C.copies - (r + 1)
  have hidx : idx < C.copies := by
    dsimp [idx]
    omega
  have hedge : Sys.Edge (C.node idx) (C.node (idx + 1)) := C.edge idx hidx
  have hroot :
      StepCtx Sys
        (Sys.recur (C.node idx) ctx (Sys.packet (C.node idx) (r + 1) payload))
        (Sys.wrap payload (Sys.recur (C.node (idx + 1)) ctx (Sys.packet (C.node (idx + 1)) r payload))) := by
    exact StepCtx.root (Sys.step_packet hedge ctx payload r)
  have hlift :=
    StepCtx.wrapNest_right (Sys := Sys) payload (C.copies - (r + 1)) hroot
  have hcount : C.copies - r = (C.copies - (r + 1)) + 1 := by
    omega
  have hnode : C.node ((C.copies - (r + 1)) + 1) = C.node (C.copies - r) := by
    simp [hcount]
  have hs :
      phase C ctx payload (r + 1) =
        GraphPacketSystem.wrapNest Sys payload (C.copies - (r + 1))
          (Sys.recur (C.node idx) ctx (Sys.packet (C.node idx) (r + 1) payload)) := by
    rfl
  have ht :
      phase C ctx payload r =
        GraphPacketSystem.wrapNest Sys payload (C.copies - (r + 1))
          (Sys.wrap payload
            (Sys.recur (C.node ((C.copies - (r + 1)) + 1)) ctx
              (Sys.packet (C.node ((C.copies - (r + 1)) + 1)) r payload))) := by
    simp [phase, hcount, hnode, GraphPacketSystem.wrapNest]
  rw [hs, ht]
  exact hlift

/-- One full certified graph cycle realizes the synchronized packet exposure. -/
theorem cycle_realized (C : CyclePath Sys) (ctx payload : Sys.T) :
    Relation.TransGen (StepCtx Sys)
      (MutualDuplicationPayloadFlow.syncSource (Sys.toPacketModel (C.node 0)) C.copies ctx payload)
      (MutualDuplicationPayloadFlow.syncTarget (Sys.toPacketModel (C.node 0)) C.copies ctx payload) := by
  have hpath :
      ∀ m, m < C.copies →
        Relation.TransGen (StepCtx Sys) (phase C ctx payload (m + 1)) (phase C ctx payload 0) := by
    intro m
    induction m with
    | zero =>
        intro hm
        exact Relation.TransGen.single (phase_step C ctx payload (r := 0) hm)
    | succ m ih =>
        intro hm
        have hstep : StepCtx Sys (phase C ctx payload (m + 2)) (phase C ctx payload (m + 1)) := by
          exact phase_step C ctx payload (r := m + 1) hm
        have htail :
            Relation.TransGen (StepCtx Sys) (phase C ctx payload (m + 1)) (phase C ctx payload 0) := by
          exact ih (by omega)
        exact Relation.TransGen.trans (Relation.TransGen.single hstep) htail
  have hstart :
      phase C ctx payload C.copies =
        MutualDuplicationPayloadFlow.syncSource (Sys.toPacketModel (C.node 0)) C.copies ctx payload := by
    simp [phase, GraphPacketSystem.toPacketModel, GraphPacketSystem.wrapNest,
      MutualDuplicationPayloadFlow.syncSource]
  have htarget :
      phase C ctx payload 0 =
        MutualDuplicationPayloadFlow.syncTarget (Sys.toPacketModel (C.node 0)) C.copies ctx payload := by
    have hzero :
        Sys.recur (C.node 0) ctx (Sys.packet (C.node 0) 0 payload) =
          Sys.recur (C.node 0) ctx Sys.empty := by
      simp [Sys.packet_zero (C.node 0) payload]
    simpa [phase, GraphPacketSystem.toPacketModel, GraphPacketSystem.wrapNest,
      MutualDuplicationPayloadFlow.syncTarget, C.closed,
      packetFlow_wrapNest_eq C payload C.copies (Sys.recur (C.node 0) ctx Sys.empty)]
      using congrArg (GraphPacketSystem.wrapNest Sys payload C.copies) hzero
  rw [← hstart, ← htarget]
  have hpred : C.copies - 1 < C.copies := by
    simpa [Nat.pred_eq_sub_one] using Nat.pred_lt (Nat.ne_of_gt C.hcopies)
  have hlast : C.copies - 1 + 1 = C.copies := by
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt C.hcopies)
  simpa [hlast] using hpath (C.copies - 1) hpred

def toCycleWitness (C : CyclePath Sys) :
    MutualDuplicationPayloadFlow.CycleWitness (Sys.toPacketModel (C.node 0)) C.copies where
  StepCtx := StepCtx Sys
  cycle_realized := cycle_realized C

theorem no_global_orients_ctx_additive
    (C : CyclePath Sys) (M : AdditiveMeasure Sys) :
    ¬ GlobalOrientsCtx Sys M.eval := by
  intro h
  have h' :
      MutualDuplicationPayloadFlow.GlobalOrientsCtx
        (toCycleWitness C) (AdditiveMeasure.toPacketModelMeasure M (C.node 0)).eval := by
    intro a b hstep
    exact h hstep
  exact
    MutualDuplicationPayloadFlow.no_global_orients_ctx_additive
      (W := toCycleWitness C)
      (A := AdditiveMeasure.toPacketModelMeasure M (C.node 0))
      (hcopies := Nat.succ_le_of_lt C.hcopies) h'

theorem no_global_orients_ctx_affine_of_wrapper_dominance
    (C : CyclePath Sys) (M : AffineMeasure Sys)
    (hdom :
      MutualDuplicationPayloadFlow.WrapperDominance
        (AffineMeasure.toPacketModelMeasure M (C.node 0)) C.copies)
    (hunbounded : ∀ q : Nat, ∃ t : Sys.T, q ≤ M.eval t) :
    ¬ GlobalOrientsCtx Sys M.eval := by
  intro h
  have h' :
      MutualDuplicationPayloadFlow.GlobalOrientsCtx
        (toCycleWitness C) (AffineMeasure.toPacketModelMeasure M (C.node 0)).eval := by
    intro a b hstep
    exact h hstep
  exact
    MutualDuplicationPayloadFlow.no_global_orients_ctx_affine_of_wrapper_dominance
      (W := toCycleWitness C)
      (A := AffineMeasure.toPacketModelMeasure M (C.node 0))
      (hdom := hdom)
      (hunbounded := hunbounded) h'

theorem no_global_orients_ctx_transparent
    (C : CyclePath Sys) (M : TransparentMeasure Sys) :
    ¬ GlobalOrientsCtx Sys M.eval := by
  intro h
  have h' :
      MutualDuplicationPayloadFlow.GlobalOrientsCtx
        (toCycleWitness C) (TransparentMeasure.toPacketModelMeasure M (C.node 0)).eval := by
    intro a b hstep
    exact h hstep
  exact
    MutualDuplicationPayloadFlow.no_global_orients_ctx_transparent
      (W := toCycleWitness C)
      (A := TransparentMeasure.toPacketModelMeasure M (C.node 0))
      (hcopies := C.hcopies) h'

theorem no_global_orients_ctx_of_scalar_projection_transparent
    (C : CyclePath Sys)
    {α : Type} (μ : Sys.T → α) (R : α → α → Prop) (π : α → Nat)
    (hproj : ∀ {u v : α}, R u v → π u < π v)
    (M : TransparentMeasure Sys)
    (hπ : ∀ t : Sys.T, π (μ t) = M.eval t) :
    ¬ DependencyPairsFragment.GlobalOrients (StepCtx Sys) μ R := by
  exact
    MutualDuplicationPayloadFlow.no_global_orients_ctx_of_scalar_projection_transparent
      (W := toCycleWitness C)
      (μ := μ) (R := R) (π := π)
      (hproj := hproj)
      (A := TransparentMeasure.toPacketModelMeasure M (C.node 0))
      (hπ := hπ)
      (hcopies := C.hcopies)

/-- Closed-path wrapper for the additive preserving raw-graph barrier. -/
theorem no_global_orients_ctx_additive_of_closedTransGen
    {i : ι} (hcycle : Relation.TransGen Sys.Edge i i)
    (M : AdditiveMeasure Sys) :
    ¬ GlobalOrientsCtx Sys M.eval :=
  no_global_orients_ctx_additive (C := ofClosedTransGen hcycle) M

/-- Round-trip SCC wrapper for the additive preserving raw-graph barrier. -/
theorem no_global_orients_ctx_additive_of_roundTrip
    {i j : ι} (hij : Relation.TransGen Sys.Edge i j) (hji : Relation.TransGen Sys.Edge j i)
    (M : AdditiveMeasure Sys) :
    ¬ GlobalOrientsCtx Sys M.eval :=
  no_global_orients_ctx_additive (C := ofRoundTrip hij hji) M

/-- Closed-path wrapper for the affine preserving raw-graph barrier. -/
theorem no_global_orients_ctx_affine_of_wrapper_dominance_of_closedTransGen
    {i : ι} (hcycle : Relation.TransGen Sys.Edge i i)
    (M : AffineMeasure Sys)
    (hdom :
      MutualDuplicationPayloadFlow.WrapperDominance
        (AffineMeasure.toPacketModelMeasure M ((ofClosedTransGen hcycle).node 0))
        (ofClosedTransGen hcycle).copies)
    (hunbounded : ∀ q : Nat, ∃ t : Sys.T, q ≤ M.eval t) :
    ¬ GlobalOrientsCtx Sys M.eval :=
  no_global_orients_ctx_affine_of_wrapper_dominance (C := ofClosedTransGen hcycle) M hdom hunbounded

/-- Round-trip SCC wrapper for the affine preserving raw-graph barrier. -/
theorem no_global_orients_ctx_affine_of_wrapper_dominance_of_roundTrip
    {i j : ι} (hij : Relation.TransGen Sys.Edge i j) (hji : Relation.TransGen Sys.Edge j i)
    (M : AffineMeasure Sys)
    (hdom :
      MutualDuplicationPayloadFlow.WrapperDominance
        (AffineMeasure.toPacketModelMeasure M ((ofRoundTrip hij hji).node 0))
        (ofRoundTrip hij hji).copies)
    (hunbounded : ∀ q : Nat, ∃ t : Sys.T, q ≤ M.eval t) :
    ¬ GlobalOrientsCtx Sys M.eval :=
  no_global_orients_ctx_affine_of_wrapper_dominance (C := ofRoundTrip hij hji) M hdom hunbounded

/-- Closed-path wrapper for the transparent preserving raw-graph barrier. -/
theorem no_global_orients_ctx_transparent_of_closedTransGen
    {i : ι} (hcycle : Relation.TransGen Sys.Edge i i)
    (M : TransparentMeasure Sys) :
    ¬ GlobalOrientsCtx Sys M.eval :=
  no_global_orients_ctx_transparent (C := ofClosedTransGen hcycle) M

/-- Round-trip SCC wrapper for the transparent preserving raw-graph barrier. -/
theorem no_global_orients_ctx_transparent_of_roundTrip
    {i j : ι} (hij : Relation.TransGen Sys.Edge i j) (hji : Relation.TransGen Sys.Edge j i)
    (M : TransparentMeasure Sys) :
    ¬ GlobalOrientsCtx Sys M.eval :=
  no_global_orients_ctx_transparent (C := ofRoundTrip hij hji) M

/-- Closed-path wrapper for the scalar-projection preserving raw-graph barrier. -/
theorem no_global_orients_ctx_of_scalar_projection_transparent_of_closedTransGen
    {i : ι} (hcycle : Relation.TransGen Sys.Edge i i)
    {α : Type} (μ : Sys.T → α) (R : α → α → Prop) (π : α → Nat)
    (hproj : ∀ {u v : α}, R u v → π u < π v)
    (M : TransparentMeasure Sys)
    (hπ : ∀ t : Sys.T, π (μ t) = M.eval t) :
    ¬ DependencyPairsFragment.GlobalOrients (StepCtx Sys) μ R :=
  no_global_orients_ctx_of_scalar_projection_transparent
    (C := ofClosedTransGen hcycle) μ R π hproj M hπ

/-- Round-trip SCC wrapper for the scalar-projection preserving raw-graph barrier. -/
theorem no_global_orients_ctx_of_scalar_projection_transparent_of_roundTrip
    {i j : ι} (hij : Relation.TransGen Sys.Edge i j) (hji : Relation.TransGen Sys.Edge j i)
    {α : Type} (μ : Sys.T → α) (R : α → α → Prop) (π : α → Nat)
    (hproj : ∀ {u v : α}, R u v → π u < π v)
    (M : TransparentMeasure Sys)
    (hπ : ∀ t : Sys.T, π (μ t) = M.eval t) :
    ¬ DependencyPairsFragment.GlobalOrients (StepCtx Sys) μ R :=
  no_global_orients_ctx_of_scalar_projection_transparent
    (C := ofRoundTrip hij hji) μ R π hproj M hπ

/-- Finite-round-trip wrapper for the additive preserving raw-graph barrier. -/
theorem no_global_orients_ctx_additive_of_finiteRoundTrip
    [Fintype ι] [DecidableEq ι] [DecidableRel Sys.Edge]
    {i j : ι}
    (hij : Reachable Sys.Edge i j) (hji : Reachable Sys.Edge j i) (hne : i ≠ j)
    (M : AdditiveMeasure Sys) :
    ¬ GlobalOrientsCtx Sys M.eval := by
  let hijT := transGen_of_reachable_of_ne (R := Sys.Edge) hij hne
  let hjiT := transGen_of_reachable_of_ne (R := Sys.Edge) hji hne.symm
  exact no_global_orients_ctx_additive_of_roundTrip hijT hjiT M

/-- Finite-round-trip wrapper for the affine preserving raw-graph barrier. -/
theorem no_global_orients_ctx_affine_of_wrapper_dominance_of_finiteRoundTrip
    [Fintype ι] [DecidableEq ι] [DecidableRel Sys.Edge]
    {i j : ι}
    (hij : Reachable Sys.Edge i j) (hji : Reachable Sys.Edge j i) (hne : i ≠ j)
    (M : AffineMeasure Sys)
    (hdom :
      let hijT := transGen_of_reachable_of_ne (R := Sys.Edge) hij hne
      let hjiT := transGen_of_reachable_of_ne (R := Sys.Edge) hji hne.symm
      let C := ofRoundTrip hijT hjiT
      MutualDuplicationPayloadFlow.WrapperDominance
        (AffineMeasure.toPacketModelMeasure M (C.node 0)) C.copies)
    (hunbounded : ∀ q : Nat, ∃ t : Sys.T, q ≤ M.eval t) :
    ¬ GlobalOrientsCtx Sys M.eval := by
  let hijT := transGen_of_reachable_of_ne (R := Sys.Edge) hij hne
  let hjiT := transGen_of_reachable_of_ne (R := Sys.Edge) hji hne.symm
  simpa [hijT, hjiT] using
    (no_global_orients_ctx_affine_of_wrapper_dominance_of_roundTrip
      (i := i) (j := j) hijT hjiT M hdom hunbounded)

/-- Finite-round-trip wrapper for the transparent preserving raw-graph barrier. -/
theorem no_global_orients_ctx_transparent_of_finiteRoundTrip
    [Fintype ι] [DecidableEq ι] [DecidableRel Sys.Edge]
    {i j : ι}
    (hij : Reachable Sys.Edge i j) (hji : Reachable Sys.Edge j i) (hne : i ≠ j)
    (M : TransparentMeasure Sys) :
    ¬ GlobalOrientsCtx Sys M.eval := by
  let hijT := transGen_of_reachable_of_ne (R := Sys.Edge) hij hne
  let hjiT := transGen_of_reachable_of_ne (R := Sys.Edge) hji hne.symm
  exact no_global_orients_ctx_transparent_of_roundTrip hijT hjiT M

/-- Finite-round-trip wrapper for the scalar-projection preserving barrier. -/
theorem no_global_orients_ctx_of_scalar_projection_transparent_of_finiteRoundTrip
    [Fintype ι] [DecidableEq ι] [DecidableRel Sys.Edge]
    {i j : ι}
    (hij : Reachable Sys.Edge i j) (hji : Reachable Sys.Edge j i) (hne : i ≠ j)
    {α : Type} (μ : Sys.T → α) (R : α → α → Prop) (π : α → Nat)
    (hproj : ∀ {u v : α}, R u v → π u < π v)
    (M : TransparentMeasure Sys)
    (hπ : ∀ t : Sys.T, π (μ t) = M.eval t) :
    ¬ DependencyPairsFragment.GlobalOrients (StepCtx Sys) μ R := by
  let hijT := transGen_of_reachable_of_ne (R := Sys.Edge) hij hne
  let hjiT := transGen_of_reachable_of_ne (R := Sys.Edge) hji hne.symm
  exact no_global_orients_ctx_of_scalar_projection_transparent_of_roundTrip
    hijT hjiT μ R π hproj M hπ

/-- Finite-SCC wrapper for the additive preserving raw-graph barrier. -/
theorem no_global_orients_ctx_additive_of_hasNontrivialSCC
    [Fintype ι] [DecidableEq ι] [DecidableRel Sys.Edge]
    (hSCC : HasNontrivialSCC Sys.Edge)
    (M : AdditiveMeasure Sys) :
    ¬ GlobalOrientsCtx Sys M.eval :=
  no_global_orients_ctx_additive_of_finiteRoundTrip
    (i := witnessSrc Sys.Edge hSCC) (j := witnessDst Sys.Edge hSCC)
    (reachable_witnessSrc_witnessDst (R := Sys.Edge) hSCC)
    (reachable_witnessDst_witnessSrc (R := Sys.Edge) hSCC)
    (witnessSrc_ne_witnessDst (R := Sys.Edge) hSCC)
    M

/-- Finite-SCC wrapper for the affine preserving raw-graph barrier. -/
theorem no_global_orients_ctx_affine_of_wrapper_dominance_of_hasNontrivialSCC
    [Fintype ι] [DecidableEq ι] [DecidableRel Sys.Edge]
    (hSCC : HasNontrivialSCC Sys.Edge)
    (M : AffineMeasure Sys)
    (hdom :
      let hij := reachable_witnessSrc_witnessDst (R := Sys.Edge) hSCC
      let hji := reachable_witnessDst_witnessSrc (R := Sys.Edge) hSCC
      let C := ofRoundTrip
        (transGen_of_reachable_of_ne (R := Sys.Edge) hij (witnessSrc_ne_witnessDst (R := Sys.Edge) hSCC))
        (transGen_of_reachable_of_ne (R := Sys.Edge) hji (witnessSrc_ne_witnessDst (R := Sys.Edge) hSCC).symm)
      MutualDuplicationPayloadFlow.WrapperDominance
        (AffineMeasure.toPacketModelMeasure M (C.node 0)) C.copies)
    (hunbounded : ∀ q : Nat, ∃ t : Sys.T, q ≤ M.eval t) :
    ¬ GlobalOrientsCtx Sys M.eval :=
  no_global_orients_ctx_affine_of_wrapper_dominance_of_finiteRoundTrip
    (i := witnessSrc Sys.Edge hSCC) (j := witnessDst Sys.Edge hSCC)
    (reachable_witnessSrc_witnessDst (R := Sys.Edge) hSCC)
    (reachable_witnessDst_witnessSrc (R := Sys.Edge) hSCC)
    (witnessSrc_ne_witnessDst (R := Sys.Edge) hSCC)
    M hdom hunbounded

/-- Finite-SCC wrapper for the transparent preserving raw-graph barrier. -/
theorem no_global_orients_ctx_transparent_of_hasNontrivialSCC
    [Fintype ι] [DecidableEq ι] [DecidableRel Sys.Edge]
    (hSCC : HasNontrivialSCC Sys.Edge)
    (M : TransparentMeasure Sys) :
    ¬ GlobalOrientsCtx Sys M.eval :=
  no_global_orients_ctx_transparent_of_finiteRoundTrip
    (i := witnessSrc Sys.Edge hSCC) (j := witnessDst Sys.Edge hSCC)
    (reachable_witnessSrc_witnessDst (R := Sys.Edge) hSCC)
    (reachable_witnessDst_witnessSrc (R := Sys.Edge) hSCC)
    (witnessSrc_ne_witnessDst (R := Sys.Edge) hSCC)
    M

/-- Finite-SCC wrapper for the scalar-projection preserving barrier. -/
theorem no_global_orients_ctx_of_scalar_projection_transparent_of_hasNontrivialSCC
    [Fintype ι] [DecidableEq ι] [DecidableRel Sys.Edge]
    (hSCC : HasNontrivialSCC Sys.Edge)
    {α : Type} (μ : Sys.T → α) (R : α → α → Prop) (π : α → Nat)
    (hproj : ∀ {u v : α}, R u v → π u < π v)
    (M : TransparentMeasure Sys)
    (hπ : ∀ t : Sys.T, π (μ t) = M.eval t) :
    ¬ DependencyPairsFragment.GlobalOrients (StepCtx Sys) μ R :=
  no_global_orients_ctx_of_scalar_projection_transparent_of_finiteRoundTrip
    (i := witnessSrc Sys.Edge hSCC) (j := witnessDst Sys.Edge hSCC)
    (reachable_witnessSrc_witnessDst (R := Sys.Edge) hSCC)
    (reachable_witnessDst_witnessSrc (R := Sys.Edge) hSCC)
    (witnessSrc_ne_witnessDst (R := Sys.Edge) hSCC)
    μ R π hproj M hπ

/-- Existential closed-cycle wrapper for the additive preserving raw-graph barrier. -/
theorem no_global_orients_ctx_additive_of_exists_closedTransGen
    {i : ι} (hex : ∃ _ : Relation.TransGen Sys.Edge i i, True)
    (M : AdditiveMeasure Sys) :
    ¬ GlobalOrientsCtx Sys M.eval := by
  rcases hex with ⟨hcycle, _⟩
  exact no_global_orients_ctx_additive_of_closedTransGen hcycle M

/-- Existential round-trip wrapper for the additive preserving raw-graph barrier. -/
theorem no_global_orients_ctx_additive_of_exists_roundTrip
    {i j : ι}
    (hex : ∃ _ : Relation.TransGen Sys.Edge i j, Relation.TransGen Sys.Edge j i)
    (M : AdditiveMeasure Sys) :
    ¬ GlobalOrientsCtx Sys M.eval := by
  rcases hex with ⟨hij, hji⟩
  exact no_global_orients_ctx_additive_of_roundTrip hij hji M

/-- Existential closed-cycle wrapper for the affine preserving raw-graph barrier. -/
theorem no_global_orients_ctx_affine_of_wrapper_dominance_of_exists_closedTransGen
    {i : ι} (hex : ∃ _ : Relation.TransGen Sys.Edge i i, True)
    (M : AffineMeasure Sys)
    (hdom :
      let C := ofClosedTransGen (Classical.choose hex)
      MutualDuplicationPayloadFlow.WrapperDominance
        (AffineMeasure.toPacketModelMeasure M (C.node 0)) C.copies)
    (hunbounded : ∀ q : Nat, ∃ t : Sys.T, q ≤ M.eval t) :
    ¬ GlobalOrientsCtx Sys M.eval := by
  rcases hex with ⟨hcycle, _⟩
  simpa [ofClosedTransGen] using
    (no_global_orients_ctx_affine_of_wrapper_dominance_of_closedTransGen
      (i := i) hcycle M hdom hunbounded)

/-- Existential round-trip wrapper for the affine preserving raw-graph barrier. -/
theorem no_global_orients_ctx_affine_of_wrapper_dominance_of_exists_roundTrip
    {i j : ι}
    (hex : ∃ _ : Relation.TransGen Sys.Edge i j, Relation.TransGen Sys.Edge j i)
    (M : AffineMeasure Sys)
    (hdom :
      let hij := Classical.choose hex
      let hji := Classical.choose_spec hex
      let C := ofRoundTrip hij hji
      MutualDuplicationPayloadFlow.WrapperDominance
        (AffineMeasure.toPacketModelMeasure M (C.node 0)) C.copies)
    (hunbounded : ∀ q : Nat, ∃ t : Sys.T, q ≤ M.eval t) :
    ¬ GlobalOrientsCtx Sys M.eval := by
  rcases hex with ⟨hij, hji⟩
  simpa [ofRoundTrip] using
    (no_global_orients_ctx_affine_of_wrapper_dominance_of_roundTrip
      (i := i) (j := j) hij hji M hdom hunbounded)

/-- Existential closed-cycle wrapper for the transparent preserving raw-graph barrier. -/
theorem no_global_orients_ctx_transparent_of_exists_closedTransGen
    {i : ι} (hex : ∃ _ : Relation.TransGen Sys.Edge i i, True)
    (M : TransparentMeasure Sys) :
    ¬ GlobalOrientsCtx Sys M.eval := by
  rcases hex with ⟨hcycle, _⟩
  exact no_global_orients_ctx_transparent_of_closedTransGen hcycle M

/-- Existential round-trip wrapper for the transparent preserving raw-graph barrier. -/
theorem no_global_orients_ctx_transparent_of_exists_roundTrip
    {i j : ι}
    (hex : ∃ _ : Relation.TransGen Sys.Edge i j, Relation.TransGen Sys.Edge j i)
    (M : TransparentMeasure Sys) :
    ¬ GlobalOrientsCtx Sys M.eval := by
  rcases hex with ⟨hij, hji⟩
  exact no_global_orients_ctx_transparent_of_roundTrip hij hji M

/-- Existential closed-cycle wrapper for the scalar-projection preserving barrier. -/
theorem no_global_orients_ctx_of_scalar_projection_transparent_of_exists_closedTransGen
    {i : ι} (hex : ∃ _ : Relation.TransGen Sys.Edge i i, True)
    {α : Type} (μ : Sys.T → α) (R : α → α → Prop) (π : α → Nat)
    (hproj : ∀ {u v : α}, R u v → π u < π v)
    (M : TransparentMeasure Sys)
    (hπ : ∀ t : Sys.T, π (μ t) = M.eval t) :
    ¬ DependencyPairsFragment.GlobalOrients (StepCtx Sys) μ R := by
  rcases hex with ⟨hcycle, _⟩
  exact no_global_orients_ctx_of_scalar_projection_transparent_of_closedTransGen hcycle μ R π hproj M hπ

/-- Existential round-trip wrapper for the scalar-projection preserving barrier. -/
theorem no_global_orients_ctx_of_scalar_projection_transparent_of_exists_roundTrip
    {i j : ι}
    (hex : ∃ _ : Relation.TransGen Sys.Edge i j, Relation.TransGen Sys.Edge j i)
    {α : Type} (μ : Sys.T → α) (R : α → α → Prop) (π : α → Nat)
    (hproj : ∀ {u v : α}, R u v → π u < π v)
    (M : TransparentMeasure Sys)
    (hπ : ∀ t : Sys.T, π (μ t) = M.eval t) :
    ¬ DependencyPairsFragment.GlobalOrients (StepCtx Sys) μ R := by
  rcases hex with ⟨hij, hji⟩
  exact no_global_orients_ctx_of_scalar_projection_transparent_of_roundTrip hij hji μ R π hproj M hπ

end CyclePath

end GraphPacketSystem

end OperatorKO7.MutualDuplicationPacketGraph
