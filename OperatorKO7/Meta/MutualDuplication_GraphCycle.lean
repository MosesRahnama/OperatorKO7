import OperatorKO7.Meta.MutualDuplication_CycleFlow
import OperatorKO7.Meta.GraphPathExtraction
import OperatorKO7.Meta.FiniteGraphReachability
import OperatorKO7.Meta.FiniteGraphSCC

/-!
# Raw-Graph Delayed-Duplication SCC Barrier

This module lifts the delayed-duplication SCC story from finite cyclic signatures to an
arbitrary directed graph equipped with:

- a shared first-order constructor interface,
- a family of graph-indexed recursors,
- local successor rules along graph edges, and
- an explicit closed cycle witness in the raw graph.

The point is not to discover SCCs automatically. The theorem is still witness-based.
But once a concrete cycle in an arbitrary graph is certified, the additive, affine,
transparent-compositional, and scalar-projection contextual barriers follow uniformly.
-/

namespace OperatorKO7.MutualDuplicationGraphCycle

open OperatorKO7.StepDuplicating
open OperatorKO7.DependencyPairsFragment
open OperatorKO7.MutualDuplicationCycleFlow
open OperatorKO7.GraphPathExtraction
open OperatorKO7.FiniteGraphReachability
open OperatorKO7.FiniteGraphSCC
open OperatorKO7.StepDuplicating.StepDuplicatingSchema

/-- A rewrite signature indexed by an arbitrary directed graph. -/
structure GraphDupSystem (ι : Type) where
  T : Type
  base : T
  succ : T → T
  wrap : T → T → T
  recur : ι → T → T → T → T
  Edge : ι → ι → Prop
  Step : T → T → Prop
  step_succ :
    ∀ {i j}, Edge i j → ∀ b s n,
      Step (recur i b s (succ n)) (wrap s (recur j b s n))

namespace GraphDupSystem

/-- Forget all but one chosen graph node and expose the ordinary duplication schema. -/
def toNodeSchema {ι : Type} (Sys : GraphDupSystem ι) (i : ι) : StepDuplicatingSchema where
  T := Sys.T
  base := Sys.base
  succ := Sys.succ
  wrap := Sys.wrap
  recur := Sys.recur i

/-- Minimal contextual relation: root steps plus right-wrapper descent. -/
inductive StepCtx {ι : Type} (Sys : GraphDupSystem ι) : Sys.T → Sys.T → Prop
| root : ∀ {a b}, Sys.Step a b → StepCtx Sys a b
| wrap_right : ∀ s {a b}, StepCtx Sys a b → StepCtx Sys (Sys.wrap s a) (Sys.wrap s b)

/-- Orientation of the induced contextual relation. -/
def GlobalOrientsCtx {ι : Type} {α : Type} (Sys : GraphDupSystem ι) (m : Sys.T → α)
    (lt : α → α → Prop) : Prop :=
  ∀ {a b : Sys.T}, StepCtx Sys a b → lt (m b) (m a)

/-- Successor iteration on the shared carrier. -/
def succIterOn {ι : Type} (Sys : GraphDupSystem ι) : Nat → Sys.T → Sys.T
  | 0, t => t
  | n + 1, t => Sys.succ (succIterOn Sys n t)

/-- Wrapper nesting on the shared carrier. -/
def wrapNest {ι : Type} (Sys : GraphDupSystem ι) (s : Sys.T) : Nat → Sys.T → Sys.T
  | 0, t => t
  | n + 1, t => wrapNest Sys s n (Sys.wrap s t)

/-- Uniform additive constructor-local measures on the graph-indexed SCC syntax. -/
structure AdditiveMeasure {ι : Type} (Sys : GraphDupSystem ι) where
  eval : Sys.T → Nat
  w_base : Nat
  w_succ : Nat
  w_wrap : Nat
  w_recur : Nat
  eval_base : eval Sys.base = w_base
  eval_succ : ∀ t, eval (Sys.succ t) = w_succ + eval t
  eval_wrap : ∀ x y, eval (Sys.wrap x y) = w_wrap + eval x + eval y
  eval_recur : ∀ i b s n, eval (Sys.recur i b s n) = w_recur + eval b + eval s + eval n
  h_wrap_pos : 1 ≤ w_wrap

/-- Uniform affine constructor-local measures on the graph-indexed SCC syntax. -/
structure AffineMeasure {ι : Type} (Sys : GraphDupSystem ι) where
  eval : Sys.T → Nat
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
  eval_base : eval Sys.base = c_base
  eval_succ : ∀ t, eval (Sys.succ t) = succ_bias + succ_scale * eval t
  eval_wrap : ∀ x y, eval (Sys.wrap x y) = wrap_const + wrap_left * eval x + wrap_right * eval y
  eval_recur :
    ∀ i b s n,
      eval (Sys.recur i b s n) =
        recur_const + recur_base * eval b + recur_step * eval s + recur_counter * eval n
  h_wrap_left_pos : 1 ≤ wrap_left
  h_wrap_right_pos : 1 ≤ wrap_right

/-- Uniform transparent-compositional measures on the graph-indexed SCC syntax. -/
structure CompositionalMeasure {ι : Type} (Sys : GraphDupSystem ι) where
  eval : Sys.T → Nat
  c_base : Nat
  c_succ : Nat → Nat
  c_wrap : Nat → Nat → Nat
  c_recur : Nat → Nat → Nat → Nat
  eval_base : eval Sys.base = c_base
  eval_succ : ∀ t, eval (Sys.succ t) = c_succ (eval t)
  eval_wrap : ∀ x y, eval (Sys.wrap x y) = c_wrap (eval x) (eval y)
  eval_recur : ∀ i b s n, eval (Sys.recur i b s n) = c_recur (eval b) (eval s) (eval n)
  wrap_subterm1 : ∀ x y, c_wrap x y > x
  wrap_subterm2 : ∀ x y, c_wrap x y > y

def AdditiveMeasure.toNodeMeasure {ι : Type} {Sys : GraphDupSystem ι}
    (M : AdditiveMeasure Sys) (i : ι) :
    StepDuplicatingSchema.AdditiveMeasure (Sys.toNodeSchema i) where
  eval := M.eval
  w_base := M.w_base
  w_succ := M.w_succ
  w_wrap := M.w_wrap
  w_recur := M.w_recur
  eval_base := M.eval_base
  eval_succ := M.eval_succ
  eval_wrap := M.eval_wrap
  eval_recur := M.eval_recur i
  h_wrap_pos := M.h_wrap_pos

def AffineMeasure.toNodeMeasure {ι : Type} {Sys : GraphDupSystem ι}
    (M : AffineMeasure Sys) (i : ι) :
    StepDuplicatingSchema.AffineMeasure (Sys.toNodeSchema i) where
  eval := M.eval
  c_base := M.c_base
  succ_bias := M.succ_bias
  succ_scale := M.succ_scale
  wrap_const := M.wrap_const
  wrap_left := M.wrap_left
  wrap_right := M.wrap_right
  recur_const := M.recur_const
  recur_base := M.recur_base
  recur_step := M.recur_step
  recur_counter := M.recur_counter
  eval_base := M.eval_base
  eval_succ := M.eval_succ
  eval_wrap := M.eval_wrap
  eval_recur := M.eval_recur i
  h_wrap_left_pos := M.h_wrap_left_pos
  h_wrap_right_pos := M.h_wrap_right_pos

def CompositionalMeasure.toNodeMeasure {ι : Type} {Sys : GraphDupSystem ι}
    (M : CompositionalMeasure Sys) (i : ι) :
    StepDuplicatingSchema.CompositionalMeasure (Sys.toNodeSchema i) where
  eval := M.eval
  c_base := M.c_base
  c_succ := M.c_succ
  c_wrap := M.c_wrap
  c_recur := M.c_recur
  eval_base := M.eval_base
  eval_succ := M.eval_succ
  eval_wrap := M.eval_wrap
  eval_recur := M.eval_recur i
  wrap_subterm1 := M.wrap_subterm1
  wrap_subterm2 := M.wrap_subterm2

namespace StepCtx

lemma wrapNest_right {ι : Type} {Sys : GraphDupSystem ι}
    (s : Sys.T) :
    ∀ n {a b : Sys.T}, StepCtx Sys a b →
      StepCtx Sys
        (GraphDupSystem.wrapNest Sys s n a)
        (GraphDupSystem.wrapNest Sys s n b) := by
  intro n
  induction n with
  | zero =>
      intro a b h
      simpa [GraphDupSystem.wrapNest] using h
  | succ n ih =>
      intro a b h
      simpa [GraphDupSystem.wrapNest] using
        ih (StepCtx.wrap_right s h)

end StepCtx

/-- A certified closed cycle in the raw graph. The graph itself may have arbitrary extra
structure; only this chosen cycle is used. -/
structure CyclePath {ι : Type} (Sys : GraphDupSystem ι) where
  copies : Nat
  hcopies : 0 < copies
  node : Nat → ι
  edge : ∀ r, r < copies → Sys.Edge (node r) (node (r + 1))
  closed : node copies = node 0

/-- Build a concrete graph cycle from any nonempty closed transitive-closure witness. -/
noncomputable def ofClosedTransGen {ι : Type} {Sys : GraphDupSystem ι} {i : ι}
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
noncomputable def ofRoundTrip {ι : Type} {Sys : GraphDupSystem ι} {i j : ι}
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

@[simp] theorem ofClosedTransGen_node0 {ι : Type} {Sys : GraphDupSystem ι} {i : ι}
    (hcycle : Relation.TransGen Sys.Edge i i) :
    (ofClosedTransGen hcycle).node 0 = i := by
  simpa [ofClosedTransGen] using (EdgePath.ofTransGen hcycle).start

@[simp] theorem ofRoundTrip_node0 {ι : Type} {Sys : GraphDupSystem ι} {i j : ι}
    (hij : Relation.TransGen Sys.Edge i j) (hji : Relation.TransGen Sys.Edge j i) :
    (ofRoundTrip hij hji).node 0 = i := by
  simpa [ofRoundTrip] using (EdgePath.ofRoundTrip hij hji).start

namespace CyclePath

variable {ι : Type} {Sys : GraphDupSystem ι}

/-- The `r`-step residual phase of one certified raw-graph cycle. -/
def phase (C : CyclePath Sys) (b s n : Sys.T) (r : Nat) : Sys.T :=
  GraphDupSystem.wrapNest Sys s (C.copies - r)
    (Sys.recur (C.node (C.copies - r)) b s
      (GraphDupSystem.succIterOn Sys r n))

lemma cycleFlow_succIter_eq (C : CyclePath Sys) :
    ∀ n t,
      GraphDupSystem.succIterOn Sys n t =
        OperatorKO7.MutualDuplicationCycleFlow.succIterOn
          (Sys.toNodeSchema (C.node 0)) n t
  | 0, t => by rfl
  | n + 1, t => by
      rw [GraphDupSystem.succIterOn, OperatorKO7.MutualDuplicationCycleFlow.succIterOn,
        cycleFlow_succIter_eq C n]
      rfl

lemma cycleFlow_wrapNest_eq (C : CyclePath Sys) (s : Sys.T) :
    ∀ n t,
      GraphDupSystem.wrapNest Sys s n t =
        OperatorKO7.MutualDuplicationCycleFlow.wrapNest
          (Sys.toNodeSchema (C.node 0)) s n t
  | 0, t => by rfl
  | n + 1, t => by
      rw [GraphDupSystem.wrapNest, OperatorKO7.MutualDuplicationCycleFlow.wrapNest,
        cycleFlow_wrapNest_eq C s n]
      rfl

lemma phase_step (C : CyclePath Sys) (b s n : Sys.T) {r : Nat} (hr : r < C.copies) :
    StepCtx Sys (phase C b s n (r + 1)) (phase C b s n r) := by
  let idx := C.copies - (r + 1)
  have hidx : idx < C.copies := by
    dsimp [idx]
    omega
  have hedge : Sys.Edge (C.node idx) (C.node (idx + 1)) := C.edge idx hidx
  have hroot :
      StepCtx Sys
        (Sys.recur (C.node idx) b s
          (Sys.succ
            (GraphDupSystem.succIterOn Sys r n)))
        (Sys.wrap s
          (Sys.recur (C.node (idx + 1)) b s
            (GraphDupSystem.succIterOn Sys r n))) := by
    exact StepCtx.root (Sys.step_succ hedge b s _)
  have hlift :=
    StepCtx.wrapNest_right (Sys := Sys) s (C.copies - (r + 1)) hroot
  have hcount : C.copies - r = (C.copies - (r + 1)) + 1 := by
    omega
  have hnode : C.node ((C.copies - (r + 1)) + 1) = C.node (C.copies - r) := by
    simp [hcount]
  have hs :
      phase C b s n (r + 1) =
        GraphDupSystem.wrapNest Sys s (C.copies - (r + 1))
          (Sys.recur (C.node idx) b s (Sys.succ (GraphDupSystem.succIterOn Sys r n))) := by
    rfl
  have ht :
      phase C b s n r =
        GraphDupSystem.wrapNest Sys s (C.copies - (r + 1))
          (Sys.wrap s
            (Sys.recur (C.node ((C.copies - (r + 1)) + 1)) b s
              (GraphDupSystem.succIterOn Sys r n))) := by
    simp [phase, hcount, hnode, GraphDupSystem.wrapNest]
  rw [hs, ht]
  exact hlift

/-- One full certified raw-graph cycle realizes the delayed duplicate. -/
theorem cycle_realized (C : CyclePath Sys) (b s n : Sys.T) :
    Relation.TransGen (StepCtx Sys)
      (OperatorKO7.MutualDuplicationCycleFlow.cycleSource
        (Sys.toNodeSchema (C.node 0)) C.copies b s n)
      (OperatorKO7.MutualDuplicationCycleFlow.cycleTarget
        (Sys.toNodeSchema (C.node 0)) C.copies b s n) := by
  have hpath :
      ∀ m, m < C.copies →
        Relation.TransGen (StepCtx Sys) (phase C b s n (m + 1)) (phase C b s n 0) := by
    intro m
    induction m with
    | zero =>
        intro hm
        exact Relation.TransGen.single (phase_step C b s n (r := 0) hm)
    | succ m ih =>
        intro hm
        have hstep : StepCtx Sys (phase C b s n (m + 2)) (phase C b s n (m + 1)) := by
          exact phase_step C b s n (r := m + 1) hm
        have htail :
            Relation.TransGen (StepCtx Sys) (phase C b s n (m + 1)) (phase C b s n 0) := by
          exact ih (by omega)
        exact Relation.TransGen.trans (Relation.TransGen.single hstep) htail
  have hstart :
      phase C b s n C.copies =
        OperatorKO7.MutualDuplicationCycleFlow.cycleSource
          (Sys.toNodeSchema (C.node 0)) C.copies b s n := by
    simp [phase, GraphDupSystem.toNodeSchema, GraphDupSystem.wrapNest,
      OperatorKO7.MutualDuplicationCycleFlow.cycleSource,
      cycleFlow_succIter_eq C C.copies n]
  have htarget :
      phase C b s n 0 =
        OperatorKO7.MutualDuplicationCycleFlow.cycleTarget
          (Sys.toNodeSchema (C.node 0)) C.copies b s n := by
    simp [phase, GraphDupSystem.toNodeSchema, GraphDupSystem.succIterOn,
      OperatorKO7.MutualDuplicationCycleFlow.cycleTarget,
      C.closed, cycleFlow_wrapNest_eq C s C.copies (Sys.recur (C.node 0) b s n)]
  rw [← hstart, ← htarget]
  have hpred : C.copies - 1 < C.copies := by
    simpa [Nat.pred_eq_sub_one] using Nat.pred_lt (Nat.ne_of_gt C.hcopies)
  have hlast : C.copies - 1 + 1 = C.copies := by
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt C.hcopies)
  simpa [hlast] using hpath (C.copies - 1) hpred

/-- The raw-graph delayed-duplication cycle yields an abstract cycle witness. -/
def toCycleWitness (C : CyclePath Sys) :
    OperatorKO7.MutualDuplicationCycleFlow.CycleWitness
      (Sys.toNodeSchema (C.node 0)) C.copies where
  StepCtx := StepCtx Sys
  cycle_realized := cycle_realized C

/-- Additive barrier for any raw-graph SCC admitting a certified delayed-duplication cycle. -/
theorem no_global_orients_ctx_additive
    (C : CyclePath Sys)
    (M : GraphDupSystem.AdditiveMeasure Sys) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) := by
  intro h
  have h' :
      OperatorKO7.MutualDuplicationCycleFlow.GlobalOrientsCtx
        (toCycleWitness C) (GraphDupSystem.AdditiveMeasure.toNodeMeasure M (C.node 0)).eval (· < ·) := by
    intro a b hstep
    exact h hstep
  exact
    OperatorKO7.MutualDuplicationCycleFlow.no_global_orients_ctx_additive
      (W := toCycleWitness C)
      (M := GraphDupSystem.AdditiveMeasure.toNodeMeasure M (C.node 0))
      (hcopies := Nat.succ_le_of_lt C.hcopies) h'

/-- Affine barrier for any raw-graph SCC admitting a certified delayed-duplication cycle. -/
theorem no_global_orients_ctx_affine_of_unbounded
    (C : CyclePath Sys)
    (M : GraphDupSystem.AffineMeasure Sys)
    (hunbounded :
      StepDuplicatingSchema.HasUnboundedRange
        (AffineOps.toDupMeasure (GraphDupSystem.AffineMeasure.toNodeMeasure M (C.node 0))
          C.copies C.hcopies)) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) := by
  intro h
  have h' :
      OperatorKO7.MutualDuplicationCycleFlow.GlobalOrientsCtx
        (toCycleWitness C) (GraphDupSystem.AffineMeasure.toNodeMeasure M (C.node 0)).eval (· < ·) := by
    intro a b hstep
    exact h hstep
  exact
    OperatorKO7.MutualDuplicationCycleFlow.no_global_orients_ctx_affine_of_unbounded
      (W := toCycleWitness C)
      (M := GraphDupSystem.AffineMeasure.toNodeMeasure M (C.node 0))
      (hcopies := C.hcopies)
      (hunbounded := hunbounded) h'

/-- Transparent-compositional barrier for any raw-graph SCC admitting a certified delayed
duplicate cycle. -/
theorem no_global_orients_ctx_compositional_transparent
    (C : CyclePath Sys) (M : GraphDupSystem.CompositionalMeasure Sys)
    (htrans : M.c_succ M.c_base = M.c_base) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) := by
  intro h
  have h' :
      OperatorKO7.MutualDuplicationCycleFlow.GlobalOrientsCtx
        (toCycleWitness C) (GraphDupSystem.CompositionalMeasure.toNodeMeasure M (C.node 0)).eval (· < ·) := by
    intro a b hstep
    exact h hstep
  exact
    OperatorKO7.MutualDuplicationCycleFlow.no_global_orients_ctx_compositional_transparent
      (W := toCycleWitness C)
      (CM := GraphDupSystem.CompositionalMeasure.toNodeMeasure M (C.node 0))
      (hcopies := C.hcopies)
      (htrans := htrans) h'

/-- Scalar-projection lift for any raw-graph SCC admitting a certified delayed duplicate
cycle. -/
theorem no_global_orients_ctx_of_scalar_projection_affine_of_unbounded
    (C : CyclePath Sys)
    {α : Type} (μ : Sys.T → α) (R : α → α → Prop) (π : α → Nat)
    (hproj : ∀ {u v : α}, R u v → π u < π v)
    (A : StepDuplicatingSchema.AffineMeasure (toDupSchema (Sys.toNodeSchema (C.node 0)) C.copies))
    (hπ : ∀ t : Sys.T, π (μ t) = A.eval t)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRange A) :
    ¬ DependencyPairsFragment.GlobalOrients (StepCtx Sys) μ R := by
  exact
    OperatorKO7.MutualDuplicationCycleFlow.no_global_orients_ctx_of_scalar_projection_affine_of_unbounded
      (W := toCycleWitness C)
      (μ := μ) (R := R) (π := π)
      (hproj := hproj) (A := A) (hπ := hπ) (hunbounded := hunbounded)

/-- Closed-path wrapper for the additive raw-graph delayed-duplication barrier. -/
theorem no_global_orients_ctx_additive_of_closedTransGen
    {i : ι} (hcycle : Relation.TransGen Sys.Edge i i)
    (M : GraphDupSystem.AdditiveMeasure Sys) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) :=
  no_global_orients_ctx_additive (C := ofClosedTransGen hcycle) M

/-- Round-trip SCC wrapper for the additive raw-graph delayed-duplication barrier. -/
theorem no_global_orients_ctx_additive_of_roundTrip
    {i j : ι} (hij : Relation.TransGen Sys.Edge i j) (hji : Relation.TransGen Sys.Edge j i)
    (M : GraphDupSystem.AdditiveMeasure Sys) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) :=
  no_global_orients_ctx_additive (C := ofRoundTrip hij hji) M

/-- Closed-path wrapper for the affine raw-graph delayed-duplication barrier. -/
theorem no_global_orients_ctx_affine_of_unbounded_of_closedTransGen
    {i : ι} (hcycle : Relation.TransGen Sys.Edge i i)
    (M : GraphDupSystem.AffineMeasure Sys)
    (hunbounded :
      StepDuplicatingSchema.HasUnboundedRange
        (AffineOps.toDupMeasure (GraphDupSystem.AffineMeasure.toNodeMeasure M i)
          (ofClosedTransGen hcycle).copies (ofClosedTransGen hcycle).hcopies)) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) :=
  no_global_orients_ctx_affine_of_unbounded (C := ofClosedTransGen hcycle) M hunbounded

/-- Round-trip SCC wrapper for the affine raw-graph delayed-duplication barrier. -/
theorem no_global_orients_ctx_affine_of_unbounded_of_roundTrip
    {i j : ι} (hij : Relation.TransGen Sys.Edge i j) (hji : Relation.TransGen Sys.Edge j i)
    (M : GraphDupSystem.AffineMeasure Sys)
    (hunbounded :
      StepDuplicatingSchema.HasUnboundedRange
        (AffineOps.toDupMeasure (GraphDupSystem.AffineMeasure.toNodeMeasure M i)
          (ofRoundTrip hij hji).copies (ofRoundTrip hij hji).hcopies)) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) :=
  no_global_orients_ctx_affine_of_unbounded (C := ofRoundTrip hij hji) M hunbounded

/-- Closed-path wrapper for the transparent raw-graph delayed-duplication barrier. -/
theorem no_global_orients_ctx_compositional_transparent_of_closedTransGen
    {i : ι} (hcycle : Relation.TransGen Sys.Edge i i)
    (M : GraphDupSystem.CompositionalMeasure Sys)
    (htrans : M.c_succ M.c_base = M.c_base) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) :=
  no_global_orients_ctx_compositional_transparent (C := ofClosedTransGen hcycle) M htrans

/-- Round-trip SCC wrapper for the transparent raw-graph delayed-duplication barrier. -/
theorem no_global_orients_ctx_compositional_transparent_of_roundTrip
    {i j : ι} (hij : Relation.TransGen Sys.Edge i j) (hji : Relation.TransGen Sys.Edge j i)
    (M : GraphDupSystem.CompositionalMeasure Sys)
    (htrans : M.c_succ M.c_base = M.c_base) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) :=
  no_global_orients_ctx_compositional_transparent (C := ofRoundTrip hij hji) M htrans

/-- Closed-path wrapper for the scalar-projection delayed-duplication barrier. -/
theorem no_global_orients_ctx_of_scalar_projection_affine_of_unbounded_of_closedTransGen
    {i : ι} (hcycle : Relation.TransGen Sys.Edge i i)
    {α : Type} (μ : Sys.T → α) (R : α → α → Prop) (π : α → Nat)
    (hproj : ∀ {u v : α}, R u v → π u < π v)
    (A : StepDuplicatingSchema.AffineMeasure
      (toDupSchema (Sys.toNodeSchema ((ofClosedTransGen hcycle).node 0))
        (ofClosedTransGen hcycle).copies))
    (hπ : ∀ t : Sys.T, π (μ t) = A.eval t)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRange A) :
    ¬ DependencyPairsFragment.GlobalOrients (StepCtx Sys) μ R :=
  no_global_orients_ctx_of_scalar_projection_affine_of_unbounded
    (C := ofClosedTransGen hcycle) μ R π hproj A hπ hunbounded

/-- Round-trip SCC wrapper for the scalar-projection delayed-duplication barrier. -/
theorem no_global_orients_ctx_of_scalar_projection_affine_of_unbounded_of_roundTrip
    {i j : ι} (hij : Relation.TransGen Sys.Edge i j) (hji : Relation.TransGen Sys.Edge j i)
    {α : Type} (μ : Sys.T → α) (R : α → α → Prop) (π : α → Nat)
    (hproj : ∀ {u v : α}, R u v → π u < π v)
    (A : StepDuplicatingSchema.AffineMeasure
      (toDupSchema (Sys.toNodeSchema ((ofRoundTrip hij hji).node 0))
        (ofRoundTrip hij hji).copies))
    (hπ : ∀ t : Sys.T, π (μ t) = A.eval t)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRange A) :
    ¬ DependencyPairsFragment.GlobalOrients (StepCtx Sys) μ R :=
  no_global_orients_ctx_of_scalar_projection_affine_of_unbounded
    (C := ofRoundTrip hij hji) μ R π hproj A hπ hunbounded

/-- Finite-round-trip wrapper for the additive delayed-duplication raw-graph barrier. -/
theorem no_global_orients_ctx_additive_of_finiteRoundTrip
    [Fintype ι] [DecidableEq ι] [DecidableRel Sys.Edge]
    {i j : ι}
    (hij : Reachable Sys.Edge i j) (hji : Reachable Sys.Edge j i) (hne : i ≠ j)
    (M : GraphDupSystem.AdditiveMeasure Sys) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) := by
  let hijT := transGen_of_reachable_of_ne (R := Sys.Edge) hij hne
  let hjiT := transGen_of_reachable_of_ne (R := Sys.Edge) hji hne.symm
  exact no_global_orients_ctx_additive_of_roundTrip hijT hjiT M

/-- Finite-round-trip wrapper for the affine delayed-duplication raw-graph barrier. -/
theorem no_global_orients_ctx_affine_of_unbounded_of_finiteRoundTrip
    [Fintype ι] [DecidableEq ι] [DecidableRel Sys.Edge]
    {i j : ι}
    (hij : Reachable Sys.Edge i j) (hji : Reachable Sys.Edge j i) (hne : i ≠ j)
    (M : GraphDupSystem.AffineMeasure Sys)
    (hunbounded :
      let hijT := transGen_of_reachable_of_ne (R := Sys.Edge) hij hne
      let hjiT := transGen_of_reachable_of_ne (R := Sys.Edge) hji hne.symm
      let C := ofRoundTrip hijT hjiT
      StepDuplicatingSchema.HasUnboundedRange
        (AffineOps.toDupMeasure (GraphDupSystem.AffineMeasure.toNodeMeasure M (C.node 0))
          C.copies C.hcopies)) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) := by
  let hijT := transGen_of_reachable_of_ne (R := Sys.Edge) hij hne
  let hjiT := transGen_of_reachable_of_ne (R := Sys.Edge) hji hne.symm
  simpa [hijT, hjiT] using
    (no_global_orients_ctx_affine_of_unbounded_of_roundTrip
      (i := i) (j := j) hijT hjiT M hunbounded)

/-- Finite-round-trip wrapper for the transparent delayed-duplication raw-graph barrier. -/
theorem no_global_orients_ctx_compositional_transparent_of_finiteRoundTrip
    [Fintype ι] [DecidableEq ι] [DecidableRel Sys.Edge]
    {i j : ι}
    (hij : Reachable Sys.Edge i j) (hji : Reachable Sys.Edge j i) (hne : i ≠ j)
    (M : GraphDupSystem.CompositionalMeasure Sys)
    (htrans : M.c_succ M.c_base = M.c_base) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) := by
  let hijT := transGen_of_reachable_of_ne (R := Sys.Edge) hij hne
  let hjiT := transGen_of_reachable_of_ne (R := Sys.Edge) hji hne.symm
  exact no_global_orients_ctx_compositional_transparent_of_roundTrip hijT hjiT M htrans

/-- Finite-round-trip wrapper for the scalar-projection delayed-duplication barrier. -/
theorem no_global_orients_ctx_of_scalar_projection_affine_of_unbounded_of_finiteRoundTrip
    [Fintype ι] [DecidableEq ι] [DecidableRel Sys.Edge]
    {i j : ι}
    (hij : Reachable Sys.Edge i j) (hji : Reachable Sys.Edge j i) (hne : i ≠ j)
    {α : Type} (μ : Sys.T → α) (R : α → α → Prop) (π : α → Nat)
    (hproj : ∀ {u v : α}, R u v → π u < π v)
    (A :
      let hijT := transGen_of_reachable_of_ne (R := Sys.Edge) hij hne
      let hjiT := transGen_of_reachable_of_ne (R := Sys.Edge) hji hne.symm
      let C := ofRoundTrip hijT hjiT
      StepDuplicatingSchema.AffineMeasure
        (toDupSchema (Sys.toNodeSchema (C.node 0)) C.copies))
    (hπ : ∀ t : Sys.T, π (μ t) = A.eval t)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRange A) :
    ¬ DependencyPairsFragment.GlobalOrients (StepCtx Sys) μ R := by
  let hijT := transGen_of_reachable_of_ne (R := Sys.Edge) hij hne
  let hjiT := transGen_of_reachable_of_ne (R := Sys.Edge) hji hne.symm
  simpa [hijT, hjiT] using
    (no_global_orients_ctx_of_scalar_projection_affine_of_unbounded_of_roundTrip
      (i := i) (j := j) hijT hjiT μ R π hproj A hπ hunbounded)

/-- Finite-SCC wrapper for the additive delayed-duplication raw-graph barrier. -/
theorem no_global_orients_ctx_additive_of_hasNontrivialSCC
    [Fintype ι] [DecidableEq ι] [DecidableRel Sys.Edge]
    (hSCC : HasNontrivialSCC Sys.Edge)
    (M : GraphDupSystem.AdditiveMeasure Sys) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) :=
  no_global_orients_ctx_additive_of_finiteRoundTrip
    (i := witnessSrc Sys.Edge hSCC) (j := witnessDst Sys.Edge hSCC)
    (reachable_witnessSrc_witnessDst (R := Sys.Edge) hSCC)
    (reachable_witnessDst_witnessSrc (R := Sys.Edge) hSCC)
    (witnessSrc_ne_witnessDst (R := Sys.Edge) hSCC)
    M

/-- Finite-SCC wrapper for the affine delayed-duplication raw-graph barrier. -/
theorem no_global_orients_ctx_affine_of_unbounded_of_hasNontrivialSCC
    [Fintype ι] [DecidableEq ι] [DecidableRel Sys.Edge]
    (hSCC : HasNontrivialSCC Sys.Edge)
    (M : GraphDupSystem.AffineMeasure Sys)
    (hunbounded :
      let hij := reachable_witnessSrc_witnessDst (R := Sys.Edge) hSCC
      let hji := reachable_witnessDst_witnessSrc (R := Sys.Edge) hSCC
      let C := ofRoundTrip
        (transGen_of_reachable_of_ne (R := Sys.Edge) hij (witnessSrc_ne_witnessDst (R := Sys.Edge) hSCC))
        (transGen_of_reachable_of_ne (R := Sys.Edge) hji (witnessSrc_ne_witnessDst (R := Sys.Edge) hSCC).symm)
      StepDuplicatingSchema.HasUnboundedRange
        (AffineOps.toDupMeasure (GraphDupSystem.AffineMeasure.toNodeMeasure M (C.node 0))
          C.copies C.hcopies)) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) :=
  no_global_orients_ctx_affine_of_unbounded_of_finiteRoundTrip
    (i := witnessSrc Sys.Edge hSCC) (j := witnessDst Sys.Edge hSCC)
    (reachable_witnessSrc_witnessDst (R := Sys.Edge) hSCC)
    (reachable_witnessDst_witnessSrc (R := Sys.Edge) hSCC)
    (witnessSrc_ne_witnessDst (R := Sys.Edge) hSCC)
    M hunbounded

/-- Finite-SCC wrapper for the transparent delayed-duplication raw-graph barrier. -/
theorem no_global_orients_ctx_compositional_transparent_of_hasNontrivialSCC
    [Fintype ι] [DecidableEq ι] [DecidableRel Sys.Edge]
    (hSCC : HasNontrivialSCC Sys.Edge)
    (M : GraphDupSystem.CompositionalMeasure Sys)
    (htrans : M.c_succ M.c_base = M.c_base) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) :=
  no_global_orients_ctx_compositional_transparent_of_finiteRoundTrip
    (i := witnessSrc Sys.Edge hSCC) (j := witnessDst Sys.Edge hSCC)
    (reachable_witnessSrc_witnessDst (R := Sys.Edge) hSCC)
    (reachable_witnessDst_witnessSrc (R := Sys.Edge) hSCC)
    (witnessSrc_ne_witnessDst (R := Sys.Edge) hSCC)
    M htrans

/-- Finite-SCC wrapper for the scalar-projection delayed-duplication barrier. -/
theorem no_global_orients_ctx_of_scalar_projection_affine_of_unbounded_of_hasNontrivialSCC
    [Fintype ι] [DecidableEq ι] [DecidableRel Sys.Edge]
    (hSCC : HasNontrivialSCC Sys.Edge)
    {α : Type} (μ : Sys.T → α) (R : α → α → Prop) (π : α → Nat)
    (hproj : ∀ {u v : α}, R u v → π u < π v)
    (A :
      let hij := reachable_witnessSrc_witnessDst (R := Sys.Edge) hSCC
      let hji := reachable_witnessDst_witnessSrc (R := Sys.Edge) hSCC
      let C := ofRoundTrip
        (transGen_of_reachable_of_ne (R := Sys.Edge) hij (witnessSrc_ne_witnessDst (R := Sys.Edge) hSCC))
        (transGen_of_reachable_of_ne (R := Sys.Edge) hji (witnessSrc_ne_witnessDst (R := Sys.Edge) hSCC).symm)
      StepDuplicatingSchema.AffineMeasure
        (toDupSchema (Sys.toNodeSchema (C.node 0)) C.copies))
    (hπ : ∀ t : Sys.T, π (μ t) = A.eval t)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRange A) :
    ¬ DependencyPairsFragment.GlobalOrients (StepCtx Sys) μ R :=
  no_global_orients_ctx_of_scalar_projection_affine_of_unbounded_of_finiteRoundTrip
    (i := witnessSrc Sys.Edge hSCC) (j := witnessDst Sys.Edge hSCC)
    (reachable_witnessSrc_witnessDst (R := Sys.Edge) hSCC)
    (reachable_witnessDst_witnessSrc (R := Sys.Edge) hSCC)
    (witnessSrc_ne_witnessDst (R := Sys.Edge) hSCC)
    μ R π hproj A hπ hunbounded

/-- Existential closed-cycle wrapper for the additive delayed-duplication raw-graph barrier. -/
theorem no_global_orients_ctx_additive_of_exists_closedTransGen
    {i : ι} (hex : ∃ _ : Relation.TransGen Sys.Edge i i, True)
    (M : GraphDupSystem.AdditiveMeasure Sys) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) := by
  rcases hex with ⟨hcycle, _⟩
  exact no_global_orients_ctx_additive_of_closedTransGen hcycle M

/-- Existential round-trip wrapper for the additive delayed-duplication raw-graph barrier. -/
theorem no_global_orients_ctx_additive_of_exists_roundTrip
    {i j : ι}
    (hex : ∃ _ : Relation.TransGen Sys.Edge i j, Relation.TransGen Sys.Edge j i)
    (M : GraphDupSystem.AdditiveMeasure Sys) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) := by
  rcases hex with ⟨hij, hji⟩
  exact no_global_orients_ctx_additive_of_roundTrip hij hji M

/-- Existential closed-cycle wrapper for the affine delayed-duplication raw-graph barrier. -/
theorem no_global_orients_ctx_affine_of_unbounded_of_exists_closedTransGen
    {i : ι} (hex : ∃ _ : Relation.TransGen Sys.Edge i i, True)
    (M : GraphDupSystem.AffineMeasure Sys)
    (hunbounded :
      let C := ofClosedTransGen (Classical.choose hex)
      StepDuplicatingSchema.HasUnboundedRange
        (AffineOps.toDupMeasure (GraphDupSystem.AffineMeasure.toNodeMeasure M (C.node 0))
          C.copies C.hcopies)) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) := by
  rcases hex with ⟨hcycle, _⟩
  simpa [ofClosedTransGen] using
    (no_global_orients_ctx_affine_of_unbounded_of_closedTransGen
      (i := i) hcycle M hunbounded)

/-- Existential round-trip wrapper for the affine delayed-duplication raw-graph barrier. -/
theorem no_global_orients_ctx_affine_of_unbounded_of_exists_roundTrip
    {i j : ι}
    (hex : ∃ _ : Relation.TransGen Sys.Edge i j, Relation.TransGen Sys.Edge j i)
    (M : GraphDupSystem.AffineMeasure Sys)
    (hunbounded :
      let hij := Classical.choose hex
      let hji := Classical.choose_spec hex
      let C := ofRoundTrip hij hji
      StepDuplicatingSchema.HasUnboundedRange
        (AffineOps.toDupMeasure (GraphDupSystem.AffineMeasure.toNodeMeasure M (C.node 0))
          C.copies C.hcopies)) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) := by
  rcases hex with ⟨hij, hji⟩
  simpa [ofRoundTrip] using
    (no_global_orients_ctx_affine_of_unbounded_of_roundTrip
      (i := i) (j := j) hij hji M hunbounded)

/-- Existential closed-cycle wrapper for the transparent delayed-duplication raw-graph barrier. -/
theorem no_global_orients_ctx_compositional_transparent_of_exists_closedTransGen
    {i : ι} (hex : ∃ _ : Relation.TransGen Sys.Edge i i, True)
    (M : GraphDupSystem.CompositionalMeasure Sys)
    (htrans : M.c_succ M.c_base = M.c_base) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) := by
  rcases hex with ⟨hcycle, _⟩
  exact no_global_orients_ctx_compositional_transparent_of_closedTransGen hcycle M htrans

/-- Existential round-trip wrapper for the transparent delayed-duplication raw-graph barrier. -/
theorem no_global_orients_ctx_compositional_transparent_of_exists_roundTrip
    {i j : ι}
    (hex : ∃ _ : Relation.TransGen Sys.Edge i j, Relation.TransGen Sys.Edge j i)
    (M : GraphDupSystem.CompositionalMeasure Sys)
    (htrans : M.c_succ M.c_base = M.c_base) :
    ¬ GlobalOrientsCtx Sys M.eval (· < ·) := by
  rcases hex with ⟨hij, hji⟩
  exact no_global_orients_ctx_compositional_transparent_of_roundTrip hij hji M htrans

/-- Existential closed-cycle wrapper for the scalar-projection delayed-duplication barrier. -/
theorem no_global_orients_ctx_of_scalar_projection_affine_of_unbounded_of_exists_closedTransGen
    {i : ι} (hex : ∃ _ : Relation.TransGen Sys.Edge i i, True)
    {α : Type} (μ : Sys.T → α) (R : α → α → Prop) (π : α → Nat)
    (hproj : ∀ {u v : α}, R u v → π u < π v)
    (A :
      let C := ofClosedTransGen (Classical.choose hex)
      StepDuplicatingSchema.AffineMeasure
        (toDupSchema (Sys.toNodeSchema (C.node 0)) C.copies))
    (hπ : ∀ t : Sys.T, π (μ t) = A.eval t)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRange A) :
    ¬ DependencyPairsFragment.GlobalOrients (StepCtx Sys) μ R := by
  rcases hex with ⟨hcycle, _⟩
  simpa [ofClosedTransGen] using
    (no_global_orients_ctx_of_scalar_projection_affine_of_unbounded_of_closedTransGen
      (i := i) hcycle μ R π hproj A hπ hunbounded)

/-- Existential round-trip wrapper for the scalar-projection delayed-duplication barrier. -/
theorem no_global_orients_ctx_of_scalar_projection_affine_of_unbounded_of_exists_roundTrip
    {i j : ι}
    (hex : ∃ _ : Relation.TransGen Sys.Edge i j, Relation.TransGen Sys.Edge j i)
    {α : Type} (μ : Sys.T → α) (R : α → α → Prop) (π : α → Nat)
    (hproj : ∀ {u v : α}, R u v → π u < π v)
    (A :
      let hij := Classical.choose hex
      let hji := Classical.choose_spec hex
      let C := ofRoundTrip hij hji
      StepDuplicatingSchema.AffineMeasure
        (toDupSchema (Sys.toNodeSchema (C.node 0)) C.copies))
    (hπ : ∀ t : Sys.T, π (μ t) = A.eval t)
    (hunbounded : StepDuplicatingSchema.HasUnboundedRange A) :
    ¬ DependencyPairsFragment.GlobalOrients (StepCtx Sys) μ R := by
  rcases hex with ⟨hij, hji⟩
  simpa [ofRoundTrip] using
    (no_global_orients_ctx_of_scalar_projection_affine_of_unbounded_of_roundTrip
      (i := i) (j := j) hij hji μ R π hproj A hπ hunbounded)

end CyclePath

end GraphDupSystem

end OperatorKO7.MutualDuplicationGraphCycle
