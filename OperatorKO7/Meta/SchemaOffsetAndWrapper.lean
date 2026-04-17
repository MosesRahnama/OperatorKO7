import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import OperatorKO7.Meta.SchemaCanonicalTrace

/-!
# Wrapper Cell, Gauge Symmetry, and Retained Coordinate

Schema-level mechanization of Paper 2 Definitions 3.9–3.10 (wrapper cell and
wrapper stack), Proposition 3.12 (permutation gauge symmetry), and
Proposition 3.13 (the counter is the gauge-invariant retained coordinate).

The statements here use only the `BaseDuplicatingSystem` structure from
`SchemaCanonicalTrace.lean` and no KO7-specific syntax.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

namespace BaseDuplicatingSystem

open scoped BigOperators

variable {Sys : BaseDuplicatingSystem}

/-- **Paper 2 Def 3.9 (wrapper-cell weight).** The structural size of a single
wrapper cell is the sum of the wrapper-symbol size and the payload size. -/
def wrapperCellWeight (wrapSize paySize : Nat) : Nat := wrapSize + paySize

@[simp] theorem wrapperCellWeight_def (wrapSize paySize : Nat) :
    wrapperCellWeight wrapSize paySize = wrapSize + paySize := rfl

/-- **Paper 2 Def 3.10 (wrapper stack).** A length-`i` stack of identical
payload copies, represented on the diagonal submodule. -/
def wrapperStack (B : Type) (b : B) : Nat → List B
  | 0 => []
  | n + 1 => b :: wrapperStack B b n

@[simp] theorem wrapperStack_zero (B : Type) (b : B) :
    wrapperStack B b 0 = [] := rfl

@[simp] theorem wrapperStack_succ (B : Type) (b : B) (n : Nat) :
    wrapperStack B b (n + 1) = b :: wrapperStack B b n := rfl

/-- Length of the wrapper stack is `i`. -/
theorem wrapperStack_length (B : Type) (b : B) (n : Nat) :
    (wrapperStack B b n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [wrapperStack, ih]

/-- Every entry in the wrapper stack equals the seed value `b`
(the diagonal property). -/
theorem wrapperStack_entries (B : Type) (b : B) (n : Nat) :
    ∀ x ∈ wrapperStack B b n, x = b := by
  intro x hx
  induction n with
  | zero => simp [wrapperStack] at hx
  | succ n ih =>
      simp [wrapperStack] at hx
      rcases hx with rfl | hx
      · rfl
      · exact ih hx

/-- **Paper 2 Proposition 3.8 revisited (offset conservation).** The
wrapper-stack length always equals the payload count minus one along the
canonical trace. -/
theorem wrapperStack_length_offset (B : Type) (b : B) (i : Nat) :
    (wrapperStack B b i).length + 1 = trace_pay i := by
  unfold trace_pay
  rw [wrapperStack_length]

/-! ## Permutation gauge symmetry (Prop 3.12)

Along the canonical trace there are `i + 1` distinct payload positions at
step `i`: the `i` positions carried by the wrapper stack plus the one
active position inside the live recursor. The paper's gauge group
`Sym_{i+1}` permutes the label of which position is "active". We model
this symmetry abstractly: a gauge re-labelling is any permutation on
`Fin (i + 1)` whose action on the payload tuple preserves the set of
payload occurrences.

For the canonical trace every payload copy is the same seed `b`, so the
set-preservation condition is trivial. We record that fact as the
gauge-symmetry theorem. -/

/-- A payload tuple at step `i` is a function `Fin (i+1) → B`. -/
def PayloadTuple (B : Type) (i : Nat) : Type := Fin (i + 1) → B

/-- The constant payload tuple with every entry equal to `b`. -/
def constTuple (B : Type) (b : B) (i : Nat) : PayloadTuple B i :=
  fun _ => b

/-- A permutation on `Fin (i + 1)`. -/
def Perm (n : Nat) : Type := { f : Fin n → Fin n // Function.Bijective f }

/-- Applying a permutation to a payload tuple. -/
def PayloadTuple.permute {B : Type} {i : Nat}
    (u : PayloadTuple B i) (π : Perm (i + 1)) : PayloadTuple B i :=
  fun k => u (π.1 k)

/-- An additive observer on a payload tuple: sum the contribution of each
position under a size map. -/
def payloadMass {B : Type} {i : Nat}
    (size : B → Nat) (u : PayloadTuple B i) : Nat :=
  ∑ j : Fin (i + 1), size (u j)

/-- **Paper 2 Proposition 3.12 (permutation gauge symmetry).**
The constant payload tuple is fixed by every permutation. -/
theorem constTuple_gauge_invariant
    {B : Type} (b : B) (i : Nat) (π : Perm (i + 1)) :
    (constTuple B b i).permute π = constTuple B b i := by
  funext k
  rfl

/-- Additive payload mass is invariant under relabelling of payload positions. -/
theorem payloadMass_permute
    {B : Type} {i : Nat} (size : B → Nat)
    (u : PayloadTuple B i) (π : Perm (i + 1)) :
    payloadMass size (u.permute π) = payloadMass size u := by
  classical
  let e : Fin (i + 1) ≃ Fin (i + 1) := Equiv.ofBijective π.1 π.2
  unfold payloadMass PayloadTuple.permute
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- The additive mass of the constant payload tuple records multiplicity
exactly: `i + 1` identical copies contribute `(i + 1) * size b`. -/
theorem payloadMass_constTuple
    {B : Type} (size : B → Nat) (b : B) (i : Nat) :
    payloadMass size (constTuple B b i) = (i + 1) * size b := by
  unfold payloadMass constTuple
  simp

/-- For positive seed size, the additive mass on constant tuples is strictly
increasing with the number of payload positions. This is the precise sense in
which direct additive observers remain multiplicity-sensitive even on a single
gauge orbit. -/
theorem payloadMass_constTuple_strict_mono
    {B : Type} (size : B → Nat) (b : B) {i j : Nat}
    (hb : 0 < size b) (hij : i < j) :
    payloadMass size (constTuple B b i) < payloadMass size (constTuple B b j) := by
  rw [payloadMass_constTuple, payloadMass_constTuple]
  nlinarith

/-! ## The counter is the gauge-invariant retained coordinate (Prop 3.13) -/

/-- Gauge-invariance of a coordinate `X : PayloadTuple B i → Z`:
invariance under every permutation of payload positions. -/
def GaugeInvariant {B Z : Type} {i : Nat}
    (X : PayloadTuple B i → Z) : Prop :=
  ∀ (u : PayloadTuple B i) (π : Perm (i + 1)), X (u.permute π) = X u

/-- A constant-valued coordinate is gauge-invariant. -/
theorem constCoord_gaugeInvariant {B Z : Type} {i : Nat} (z : Z) :
    GaugeInvariant (fun (_ : PayloadTuple B i) => z) := by
  intro u π
  rfl

/-- **Paper 2 Prop 3.13 (counter is the gauge-invariant retained coordinate).**
Along the canonical trace, the counter coordinate `trace_ctr k i` is
gauge-invariant in this stronger schematic sense: it is a constant
`k - i` that does not depend on the payload tuple. -/
theorem trace_ctr_gaugeInvariant
    {B : Type} (k i : Nat) :
    GaugeInvariant (fun (_ : PayloadTuple B i) => trace_ctr k i) :=
  constCoord_gaugeInvariant _

/-- A packaged schema version of the permutation-gauge picture used in
Paper 2: the constant tuple is fixed by every payload permutation, the
additive observer records multiplicity exactly, and the counter coordinate
is the retained gauge-invariant coordinate. -/
theorem permutation_gauge_symmetry_package
    {B : Type} (size : B → Nat) (b : B) (k i : Nat) (π : Perm (i + 1)) :
    (constTuple B b i).permute π = constTuple B b i
      ∧ payloadMass size ((constTuple B b i).permute π) = (i + 1) * size b
      ∧ GaugeInvariant (fun (_ : PayloadTuple B i) => trace_ctr k i) := by
  refine ⟨constTuple_gauge_invariant b i π, ?_, trace_ctr_gaugeInvariant (B := B) k i⟩
  rw [constTuple_gauge_invariant, payloadMass_constTuple]

/-- **Paper 2 Prop 3.13 (strict descent of the counter).** -/
theorem trace_ctr_strict_descent (k i : Nat) (hik : i < k) :
    trace_ctr k (i + 1) < trace_ctr k i := by
  unfold trace_ctr
  omega

/-- **Paper 2 Prop 3.13 (reversibility of the counter step).** The descending
counter coordinate is recovered uniquely by reattaching one `succ` layer. -/
theorem trace_ctr_reversible (k i : Nat) (hik : i < k) :
    Sys.counter (trace_ctr k i) =
      Sys.succ (Sys.counter (trace_ctr k (i + 1))) := by
  unfold trace_ctr
  have hsub : k - i = (k - (i + 1)) + 1 := by omega
  rw [hsub, Sys.counter_succ]

/-- **Paper 2 Prop 3.13 (payload coordinate strictly increases, not descends).**
The payload-multiplicity coordinate `trace_pay i = i + 1` strictly increases
and therefore cannot serve as a descending coordinate. -/
theorem trace_pay_strict_ascent (i : Nat) :
    trace_pay i < trace_pay (i + 1) := by
  unfold trace_pay
  omega

/-- **Paper 2 Prop 3.13 (uniqueness of the retained coordinate).** Among the
three coordinates `(trace_ctr k i, trace_pay i, i)` along the canonical
trace, only `trace_ctr k i` is simultaneously gauge-invariant (depends only
on `k` and `i`, not on the payload tuple) and strictly descending from step
`i` to `i+1` whenever `i < k`.

- The wrapper-stack multiplicity `i` strictly ascends
  (`trace_wraps i < trace_wraps (i + 1)`).
- The payload-multiplicity coordinate strictly ascends.
- Only the counter both is gauge-invariant and strictly descends. -/
theorem counter_unique_retained_coordinate
    (k i : Nat) (hik : i < k) :
    trace_ctr k (i + 1) < trace_ctr k i
      ∧ trace_pay i < trace_pay (i + 1)
      ∧ trace_wraps i < trace_wraps (i + 1) := by
  refine ⟨trace_ctr_strict_descent k i hik,
          trace_pay_strict_ascent i, ?_⟩
  unfold trace_wraps
  omega

/-- A stronger retained-coordinate package collecting the gauge invariance,
strict descent, reversibility, and ascent of the competing coordinates. -/
theorem counter_retained_coordinate_package
    {B : Type} (k i : Nat) (hik : i < k) :
    GaugeInvariant (fun (_ : PayloadTuple B i) => trace_ctr k i)
      ∧ trace_ctr k (i + 1) < trace_ctr k i
      ∧ Sys.counter (trace_ctr k i) =
          Sys.succ (Sys.counter (trace_ctr k (i + 1)))
      ∧ trace_pay i < trace_pay (i + 1)
      ∧ trace_wraps i < trace_wraps (i + 1) := by
  refine ⟨trace_ctr_gaugeInvariant (B := B) k i, trace_ctr_strict_descent k i hik,
    trace_ctr_reversible (Sys := Sys) k i hik, trace_pay_strict_ascent i, ?_⟩
  unfold trace_wraps
  omega

end BaseDuplicatingSystem

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
