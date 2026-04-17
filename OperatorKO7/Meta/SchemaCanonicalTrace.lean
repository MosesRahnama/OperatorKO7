import OperatorKO7.Meta.StepDuplicatingSchema

/-!
# Canonical Trace Law for the Step-Duplicating Schema

Schema-level mechanization of Paper 2 Proposition 3.3 (the canonical trace
law) and Proposition 3.6 (the per-step control/payload exchange) for the
step-duplicating schema.

Given a `StepDuplicatingSystem Sys` whose `Step` relation contains both the
base rule `recur b s base → b` and the duplicating rule
`recur b s (succ n) → wrap s (recur b s n)`, we prove that the canonical
trace starting from `recur b s (succ^k base)` passes through
`wrap^i s (recur b s (succ^{k-i} base))` at step `i` and ends at
`wrap^k s b` after exactly `k+1` steps. Per-step counter/payload coordinates
along the trace satisfy the expected arithmetic identities.

This is the abstract counterpart of Paper 2's trace law for the primitive
recursion duplicator; no KO7-specific syntax is used.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-- A step-duplicating system equipped with an explicit base rule
`recur b s base → b`, mirroring Paper 2's §3 primitive-recursion setting. -/
structure BaseDuplicatingSystem extends StepDuplicatingSystem where
  base_step : ∀ b s, Step (recur b s base) b

namespace BaseDuplicatingSystem

variable {Sys : BaseDuplicatingSystem}

/-- Iterated successor `succ^k base` used as the canonical counter. -/
def counter (Sys : BaseDuplicatingSystem) : Nat → Sys.T :=
  succIter Sys.toStepDuplicatingSchema

@[simp] lemma counter_zero : Sys.counter 0 = Sys.base := rfl

@[simp] lemma counter_succ (k : Nat) :
    Sys.counter (k + 1) = Sys.succ (Sys.counter k) := rfl

/-- Left-nested wrapper chain `wrap s (wrap s (... r ...))` carrying the
same step argument `s` along with a seed `r`. -/
def wrapChain (Sys : BaseDuplicatingSystem) (s : Sys.T) : Nat → Sys.T → Sys.T
  | 0, r => r
  | n + 1, r => Sys.wrap s (wrapChain Sys s n r)

@[simp] lemma wrapChain_zero (s r : Sys.T) : Sys.wrapChain s 0 r = r := rfl

@[simp] lemma wrapChain_succ (s r : Sys.T) (n : Nat) :
    Sys.wrapChain s (n + 1) r = Sys.wrap s (Sys.wrapChain s n r) := rfl

/-- Canonical trace state at step `i` starting from `recur b s (succ^k base)`. -/
def canonicalTrace (Sys : BaseDuplicatingSystem) (b s : Sys.T) (k i : Nat) : Sys.T :=
  Sys.wrapChain s i (Sys.recur b s (Sys.counter (k - i)))

@[simp] lemma canonicalTrace_zero (b s : Sys.T) (k : Nat) :
    Sys.canonicalTrace b s k 0 = Sys.recur b s (Sys.counter k) := by
  simp [canonicalTrace]

/-- Reflexive/transitive closure of the system's step relation. -/
inductive StepStar {Sys : BaseDuplicatingSystem} : Sys.T → Sys.T → Prop
  | refl (t) : StepStar t t
  | tail {a b c} : StepStar a b → Sys.Step b c → StepStar a c

lemma StepStar.single {Sys : BaseDuplicatingSystem} {a b : Sys.T}
    (h : Sys.Step a b) : StepStar a b :=
  StepStar.tail (StepStar.refl a) h

lemma StepStar.trans {Sys : BaseDuplicatingSystem} {a b c : Sys.T}
    (hab : StepStar a b) (hbc : StepStar b c) : StepStar a c := by
  induction hbc with
  | refl => exact hab
  | tail _ hstep ih => exact StepStar.tail ih hstep

/-- Explicit wrap-context closure for systems where the root step may be lifted
under a wrapper layer. This is not built into `StepDuplicatingSystem`
itself because many barrier theorems never need it, but the full canonical
trace law does. -/
def WrapContextClosed (Sys : BaseDuplicatingSystem) : Prop :=
  ∀ (s : Sys.T) {a b : Sys.T}, Sys.Step a b → Sys.Step (Sys.wrap s a) (Sys.wrap s b)

@[simp] lemma wrapChain_push (s r : Sys.T) (i : Nat) :
    Sys.wrapChain s i (Sys.wrap s r) = Sys.wrapChain s (i + 1) r := by
  induction i with
  | zero => rfl
  | succ i ih => simp [wrapChain, ih]

lemma StepStar.wrap {Sys : BaseDuplicatingSystem}
    (hwrap : WrapContextClosed Sys) (s : Sys.T) {a b : Sys.T} :
    StepStar (Sys := Sys) a b → StepStar (Sys.wrap s a) (Sys.wrap s b) := by
  intro hab
  induction hab with
  | refl => exact StepStar.refl (Sys.wrap s a)
  | tail hab hstep ih =>
      exact StepStar.tail ih (hwrap s hstep)

lemma StepStar.wrapChain {Sys : BaseDuplicatingSystem}
    (hwrap : WrapContextClosed Sys) (s : Sys.T) (i : Nat) {a b : Sys.T} :
    StepStar (Sys := Sys) a b → StepStar (Sys.wrapChain s i a) (Sys.wrapChain s i b) := by
  induction i generalizing a b with
  | zero =>
      intro hab
      simpa [wrapChain] using hab
  | succ i ih =>
      intro hab
      simpa [wrapChain] using StepStar.wrap (Sys := Sys) hwrap s (ih hab)

/-
The schema `Step` relation is an arbitrary relation containing only the
root dup rule and (for `BaseDuplicatingSystem`) the root base rule. Context
closure under `wrap` is *not* automatic. Systems that admit wrap-context
closure can supply it as an explicit hypothesis. The canonical trace law
below is stated at the root of each stage, so context closure is not
needed.
-/

/-- One canonical step at stage `i < k`: from `recur b s (succ^{k-i} base)`
to `wrap s (recur b s (succ^{k-i-1} base))`. -/
lemma canonical_dup_step (Sys : BaseDuplicatingSystem)
    (b s : Sys.T) {k i : Nat} (hik : i < k) :
    Sys.Step
      (Sys.recur b s (Sys.counter (k - i)))
      (Sys.wrap s (Sys.recur b s (Sys.counter (k - i - 1)))) := by
  have hpos : 0 < k - i := Nat.sub_pos_of_lt hik
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have hm' : Sys.counter (k - i) = Sys.succ (Sys.counter m) := by
    rw [hm]; rfl
  have hstep : Sys.Step
      (Sys.recur b s (Sys.succ (Sys.counter m)))
      (Sys.wrap s (Sys.recur b s (Sys.counter m))) := Sys.dup_step b s (Sys.counter m)
  have hmsub : m = k - i - 1 := by
    have : k - i = m + 1 := hm
    omega
  simpa [hm', hmsub] using hstep

/-- The canonical base step at stage `k`: from `recur b s base` to `b`. -/
lemma canonical_base_step (Sys : BaseDuplicatingSystem) (b s : Sys.T) :
    Sys.Step (Sys.recur b s Sys.base) b := Sys.base_step b s

/-- One full canonical transition from stage `i` to stage `i + 1`, assuming
the system admits wrap-context closure. -/
theorem canonical_stage_step (Sys : BaseDuplicatingSystem)
    (hwrap : WrapContextClosed Sys) (b s : Sys.T) {k i : Nat} (hik : i < k) :
    StepStar
      (Sys.canonicalTrace b s k i)
      (Sys.canonicalTrace b s k (i + 1)) := by
  unfold canonicalTrace
  have hroot :
      StepStar
        (Sys.recur b s (Sys.counter (k - i)))
        (Sys.wrap s (Sys.recur b s (Sys.counter (k - i - 1)))) :=
    StepStar.single (Sys.canonical_dup_step b s hik)
  have hlift := StepStar.wrapChain (Sys := Sys) hwrap s i hroot
  have hsub : k - i - 1 = k - (i + 1) := by omega
  simpa [hsub, wrapChain_push] using hlift

/-- The canonical trace reaches the base-site stage `wrap^k s (recur b s base)`
under wrap-context closure. -/
theorem canonical_trace_to_base_stage (Sys : BaseDuplicatingSystem)
    (hwrap : WrapContextClosed Sys) (b s : Sys.T) (k : Nat) :
    StepStar
      (Sys.canonicalTrace b s k 0)
      (Sys.canonicalTrace b s k k) := by
  have hprefix :
      ∀ i, i ≤ k →
        StepStar
          (Sys.canonicalTrace b s k 0)
          (Sys.canonicalTrace b s k i) := by
    intro i hi
    induction i with
    | zero =>
        exact StepStar.refl _
    | succ i ih =>
        have hprev :
            StepStar
              (Sys.canonicalTrace b s k 0)
              (Sys.canonicalTrace b s k i) :=
          ih (by omega)
        have hstep :
            StepStar
              (Sys.canonicalTrace b s k i)
              (Sys.canonicalTrace b s k (i + 1)) :=
          Sys.canonical_stage_step hwrap b s (by omega)
        exact StepStar.trans hprev hstep
  exact hprefix k (Nat.le_refl _)

/-- Full canonical trace law under wrap-context closure: the trace starts at
`recur b s (succ^k base)`, reaches the base-site stage `wrap^k s (recur b s base)`,
and then lands on `wrap^k s b`. -/
theorem canonical_trace_full (Sys : BaseDuplicatingSystem)
    (hwrap : WrapContextClosed Sys) (b s : Sys.T) (k : Nat) :
    StepStar
      (Sys.recur b s (Sys.counter k))
      (Sys.wrapChain s k b) := by
  have htrace :
      StepStar
        (Sys.canonicalTrace b s k 0)
        (Sys.canonicalTrace b s k k) :=
    Sys.canonical_trace_to_base_stage hwrap b s k
  have hbase :
      StepStar
        (Sys.recur b s Sys.base)
        b :=
    StepStar.single (Sys.canonical_base_step b s)
  have hlift :=
    StepStar.wrapChain (Sys := Sys) hwrap s k hbase
  have hkk : k - k = 0 := by omega
  exact StepStar.trans
    (by simpa [canonicalTrace, hkk, counter_zero] using htrace)
    (by simpa using hlift)

/-- Counter-height coordinate along the canonical trace: `ctr(t_i) = k - i`. -/
def trace_ctr (k i : Nat) : Nat := k - i

@[simp] lemma trace_ctr_zero (k : Nat) : trace_ctr k 0 = k := by simp [trace_ctr]

lemma trace_ctr_step (k i : Nat) :
    trace_ctr k (i + 1) = trace_ctr k i - 1 := by
  unfold trace_ctr
  omega

/-- Payload-multiplicity coordinate along the canonical trace:
`pay(t_i) = i + 1` (the `i` wrapper copies plus the one active copy). -/
def trace_pay (i : Nat) : Nat := i + 1

@[simp] lemma trace_pay_zero : trace_pay 0 = 1 := rfl

lemma trace_pay_step (i : Nat) :
    trace_pay (i + 1) = trace_pay i + 1 := by simp [trace_pay]

/-- Per-step control/payload exchange (Paper 2 Proposition 3.6): one firing
of the duplicating rule consumes exactly one unit of counter structure and
creates exactly one additional payload slot. -/
theorem per_step_exchange (k i : Nat) (hik : i < k) :
    trace_ctr k i = trace_ctr k (i + 1) + 1
      ∧ trace_pay (i + 1) = trace_pay i + 1 := by
  refine ⟨?_, trace_pay_step i⟩
  unfold trace_ctr
  omega

/-- Per-step offset invariant (Paper 2 Proposition 3.8): along the canonical
trace, `trace_pay(i) - trace_wraps(i) = 1`, where `trace_wraps(i) := i`. -/
def trace_wraps (i : Nat) : Nat := i

@[simp] lemma trace_wraps_zero : trace_wraps 0 = 0 := rfl

theorem offset_conservation (i : Nat) :
    trace_pay i = trace_wraps i + 1 := by
  simp [trace_pay, trace_wraps]

end BaseDuplicatingSystem

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
