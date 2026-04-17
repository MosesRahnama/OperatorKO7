/-!
# Seed–Carrier Factorization Criterion

Schema-level mechanization of Paper 2 Definition 3.21, Proposition 3.22, and
Corollary 3.23. This file is deliberately *structure-free*: the statement
does not depend on `StepDuplicatingSchema` at all, only on families of
functions on diagonal submodules. The result is the formal heart of Paper 2's
Shannon-side validator: a payload observable factors through the seed-collapse
maps if and only if it is insensitive to carrier multiplicity along the
diagonal.

We also expose the two named families from Corollary 3.23:

- the direct additive `ℓ¹` reading `O_i^{(1)}(u) = |b|·(i+1)`, which does NOT
  factor through `c_i`;
- the seed-only observable `O_i^{(seed)}(u) = |b|`, which does factor through
  `c_i`.
-/

namespace OperatorKO7.SchemaSeedCarrier

/-- The diagonal submodule `Δ_{i+1} = {(c, …, c) : c ∈ B}` of `B^{i+1}`.
Rather than indexing by arity, we represent a diagonal element directly by
its shared seed value. The arity `i` is kept as a parameter so that
observables `O_i` can depend on it. -/
def Diagonal (B : Type) : Type := B

/-- The collapse map `c_i : Δ_{i+1} → B` that forgets carrier multiplicity
and retains only the shared seed value. -/
def collapse (B : Type) : Diagonal B → B := id

@[simp] theorem collapse_apply (B : Type) (c : B) :
    collapse B c = c := rfl

/-- A family of payload observables indexed by arity. Each `O i` is a
function on the diagonal; the codomain `Z` is shared across the family. -/
structure PayloadObservable (B Z : Type) where
  obs : Nat → Diagonal B → Z

namespace PayloadObservable

variable {B Z : Type}

/-- Carrier-multiplicity insensitivity along the diagonal:
for every seed `c` and all arities `i, j`, `O_i(c,…,c) = O_j(c,…,c)`. -/
def CarrierInsensitive (O : PayloadObservable B Z) : Prop :=
  ∀ (c : B) (i j : Nat), O.obs i c = O.obs j c

/-- Factorization through the seed-collapse maps: there is a common map
`Ō : B → Z` with `O_i = Ō ∘ c_i` on every `Δ_{i+1}`. -/
def FactorsThroughCollapse (O : PayloadObservable B Z) : Prop :=
  ∃ Obar : B → Z, ∀ (i : Nat) (c : B), O.obs i c = Obar (collapse B c)

/-- **Paper 2 Proposition 3.22 (seed-carrier factorization criterion).**
A payload observable family is insensitive to carrier multiplicity along the
diagonal if and only if it factors through the seed-collapse maps. -/
theorem factorization_criterion (O : PayloadObservable B Z) :
    CarrierInsensitive O ↔ FactorsThroughCollapse O := by
  constructor
  · intro hins
    refine ⟨fun c => O.obs 0 c, ?_⟩
    intro i c
    show O.obs i c = O.obs 0 (collapse B c)
    rw [collapse_apply]
    exact hins c i 0
  · rintro ⟨Obar, hfact⟩ c i j
    have hi := hfact i c
    have hj := hfact j c
    exact hi.trans hj.symm

/-- Uniqueness clause of Proposition 3.22: the factoring map `Ō` is
determined by the observable on the diagonal. -/
theorem factorization_unique (O : PayloadObservable B Z)
    (Obar Obar' : B → Z)
    (h  : ∀ (i : Nat) (c : B), O.obs i c = Obar  (collapse B c))
    (h' : ∀ (i : Nat) (c : B), O.obs i c = Obar' (collapse B c)) :
    ∀ c, Obar c = Obar' c := by
  intro c
  have h0 := h 0 c
  have h0' := h' 0 c
  rw [collapse_apply] at h0 h0'
  exact h0.symm.trans h0'

end PayloadObservable

open PayloadObservable

/-- The direct additive `ℓ¹` reading: `O_i^{(1)}(u) = (i+1) · |b|`, where the
"size" function `|·| : B → Nat` is an arbitrary weight and the argument `u`
on the diagonal is identified with its shared seed `c ∈ B`. -/
def additiveObservable (size : B → Nat) : PayloadObservable B Nat where
  obs i c := (i + 1) * size c

/-- The seed-only observable `O_i^{(seed)}(u) = |b|`. -/
def seedObservable (size : B → Nat) : PayloadObservable B Nat where
  obs _ c := size c

/-- **Paper 2 Corollary 3.23 (seed-only observable factors).** The seed-only
observable is carrier-insensitive and factors through the collapse maps with
witness `Ō := size`. -/
theorem seedObservable_factors (size : B → Nat) :
    FactorsThroughCollapse (seedObservable (B := B) size) := by
  refine ⟨size, ?_⟩
  intro i c
  rfl

/-- **Paper 2 Corollary 3.23 (additive reading does NOT factor).** Whenever
there exists a seed with positive size, the additive `ℓ¹` observable is not
carrier-insensitive and hence does not factor through the collapse maps. -/
theorem additiveObservable_not_factors (size : B → Nat)
    (h : ∃ c : B, 0 < size c) :
    ¬ FactorsThroughCollapse (additiveObservable (B := B) size) := by
  rw [← factorization_criterion]
  intro hins
  obtain ⟨c, hpos⟩ := h
  have h01 : (additiveObservable size).obs 0 c
      = (additiveObservable size).obs 1 c := hins c 0 1
  show False
  unfold additiveObservable at h01
  simp at h01
  omega

end OperatorKO7.SchemaSeedCarrier
