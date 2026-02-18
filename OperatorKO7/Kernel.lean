namespace OperatorKO7

/-!
Kernel definitions for the KO7 calculus.

Why this file exists:
- Defines the core syntax (`Trace`) and the full rewrite relation (`Step`) for the KO7 kernel.
- `Step` is the *full* kernel relation (8 unconditional rules).
- The certified artifact is proved for a guarded subrelation `SafeStep` defined in
  `OperatorKO7/Meta/SafeStep_Core.lean`.
-/

/-- The KO7 term language (7 constructors). -/
inductive Trace : Type
| void : Trace
| delta : Trace → Trace
| integrate : Trace → Trace
| merge : Trace → Trace → Trace
| app : Trace → Trace → Trace
| recΔ : Trace → Trace → Trace → Trace
| eqW : Trace → Trace → Trace
open Trace

/-- The full kernel reduction relation (8 unconditional root rules). -/
inductive Step : Trace → Trace → Prop
| R_int_delta : ∀ t, Step (integrate (delta t)) void
| R_merge_void_left : ∀ t, Step (merge void t) t
| R_merge_void_right : ∀ t, Step (merge t void) t
| R_merge_cancel : ∀ t, Step (merge t t) t
| R_rec_zero : ∀ b s, Step (recΔ b s void) b
| R_rec_succ : ∀ b s n, Step (recΔ b s (delta n)) (app s (recΔ b s n))
| R_eq_refl : ∀ a, Step (eqW a a) void
| R_eq_diff : ∀ a b, Step (eqW a b) (integrate (merge a b))

/-- Reflexive-transitive closure of the kernel step relation `Step`. -/
inductive StepStar : Trace → Trace → Prop
| refl : ∀ t, StepStar t t
| tail : ∀ {a b c}, Step a b → StepStar b c → StepStar a c

/-- Normal forms for the full kernel relation: no outgoing `Step`. -/
def NormalForm (t : Trace) : Prop := ¬ ∃ u, Step t u

/-- Transitivity of `StepStar` (concatenation of two multi-step reductions). -/
theorem stepstar_trans {a b c : Trace} (h1 : StepStar a b) (h2 : StepStar b c) : StepStar a c := by
  induction h1 with
  | refl => exact h2
  | tail hab _ ih => exact StepStar.tail hab (ih h2)

/-- Any single `Step` is also a `StepStar`. -/
theorem stepstar_of_step {a b : Trace} (h : Step a b) : StepStar a b :=
  StepStar.tail h (StepStar.refl b)

/-- If `a` is a normal form, then any `a ⇒* b` must be trivial (`b = a`). -/
theorem nf_no_stepstar_forward {a b : Trace} (hnf : NormalForm a) (h : StepStar a b) : a = b :=
  match h with
  | StepStar.refl _ => rfl
  | StepStar.tail hs _ => False.elim (hnf ⟨_, hs⟩)

end OperatorKO7
