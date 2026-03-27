import Mathlib

/-!
# Graph Path Extraction Utilities

This module packages a small generic bridge from `Relation.TransGen` proofs to explicit
edge-indexed path witnesses. It is intentionally narrow and purely structural: it does
not discover paths algorithmically, but once a nonempty transitive-closure proof is
available it reconstructs a concrete node sequence with per-edge certificates.
-/

namespace OperatorKO7.GraphPathExtraction

/-- A concrete nonempty edge path from `a` to `b`. -/
structure EdgePath {α : Type} (R : α → α → Prop) (a b : α) where
  len : Nat
  hlen : 0 < len
  node : Nat → α
  start : node 0 = a
  finish : node len = b
  edge : ∀ r, r < len → R (node r) (node (r + 1))

namespace EdgePath

variable {α : Type} {R : α → α → Prop} {a b c : α}

/-- Single-edge path. -/
def single (h : R a b) : EdgePath R a b where
  len := 1
  hlen := by omega
  node
    | 0 => a
    | _ + 1 => b
  start := rfl
  finish := rfl
  edge := by
    intro r hr
    have : r = 0 := by omega
    subst this
    simpa using h

/-- Prepend one certified edge to a concrete path. -/
def cons (h : R a b) (p : EdgePath R b c) : EdgePath R a c where
  len := p.len + 1
  hlen := by omega
  node
    | 0 => a
    | n + 1 => p.node n
  start := rfl
  finish := by simpa using p.finish
  edge := by
    intro r hr
    cases r with
    | zero =>
        simpa [p.start] using h
    | succ r =>
        have hr' : r < p.len := by omega
        simpa using p.edge r hr'

/-- Concatenate two concrete paths with matching endpoint / startpoint. -/
def append (p : EdgePath R a b) (q : EdgePath R b c) : EdgePath R a c where
  len := p.len + q.len
  hlen := Nat.add_pos_left p.hlen q.len
  node := fun n =>
    if h : n < p.len then p.node n else q.node (n - p.len)
  start := by
    have h : 0 < p.len := p.hlen
    simp [h, p.start]
  finish := by
    have h : ¬ p.len + q.len < p.len := by omega
    have hsub : p.len + q.len - p.len = q.len := by omega
    simp [h, hsub, q.finish]
  edge := by
    intro r hr
    by_cases hrp : r < p.len
    · by_cases hp : r + 1 < p.len
      · simp [hrp, hp]
        exact p.edge r hrp
      · have hEq : r + 1 = p.len := by omega
        have hed := p.edge r hrp
        simpa [hrp, hEq, p.finish, q.start] using hed
    · have hq : r - p.len < q.len := by omega
      have hp' : ¬ r + 1 < p.len := by omega
      have hsucc : r + 1 - p.len = (r - p.len) + 1 := by omega
      simp [hrp, hp', hsucc]
      exact q.edge (r - p.len) hq

/-- A nonempty transitive-closure proof carries a concrete edge path witness. -/
theorem nonempty_ofTransGen (h : Relation.TransGen R a b) : Nonempty (EdgePath R a b) := by
  induction h with
  | single h =>
      exact ⟨single h⟩
  | tail hab hbc ih =>
      rcases ih with ⟨p⟩
      exact ⟨append p (single hbc)⟩

/-- Extract a concrete edge path from a nonempty transitive-closure proof. -/
noncomputable def ofTransGen (h : Relation.TransGen R a b) : EdgePath R a b :=
  Classical.choice (nonempty_ofTransGen h)

/-- Concatenate two extracted transitive-closure paths. -/
noncomputable def ofRoundTrip (hab : Relation.TransGen R a b) (hbc : Relation.TransGen R b c) :
    EdgePath R a c :=
  append (ofTransGen hab) (ofTransGen hbc)

end EdgePath

end OperatorKO7.GraphPathExtraction
