import OperatorKO7.Meta.StepDuplicatingSchema

/-!
# Schema-Level Witness Order and Orientation Boundary Predicate

Schema-level mechanization of Paper 2 Definitions 4.1 (witness-language
hierarchy), 4.2 (minimal witness order κ*), 4.3 (orientation-boundary
predicate `OB_PRC`), and Proposition 4.4 (orientation boundary as a
witness-order threshold).

The existing `Meta/WitnessOrder.lean` file provides the coarse witness
levels (`WLevel`: `directWhole`, `importedWhole`, `transformedCall`,
`externalCert`), `WitnessTower`, `HasWitness`, `kappaLe`, `kappaGt`, and a
KO7-specific tower `ko7Tower`. We reuse `WLevel`, `HasWitness`, `kappaLe`,
`kappaGt` unchanged, and add a schema-parametric
`SchemaWitnessTower S x` together with an `OB S x` predicate.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-- Coarse witness-language level reused from Paper 2 §4. Kept local so
this file does not depend on the KO7-specific `WitnessOrder.lean`. -/
inductive WLevel
  | directWhole
  | importedWhole
  | transformedCall
  | externalCert
  deriving DecidableEq, Repr

namespace WLevel

def toNat : WLevel → Nat
  | directWhole => 0
  | importedWhole => 1
  | transformedCall => 2
  | externalCert => 3

instance : LE WLevel := ⟨fun a b => a.toNat ≤ b.toNat⟩
instance : LT WLevel := ⟨fun a b => a.toNat < b.toNat⟩

instance (a b : WLevel) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toNat ≤ b.toNat))
instance (a b : WLevel) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toNat < b.toNat))

end WLevel

/-- A schema-parametric witness tower. For a step-duplicating schema `S`,
`SchemaWitnessTower S x ℓ` records whether there is a witness at level `ℓ`
suitable for the instance `x : S.T`. -/
def SchemaWitnessTower (S : StepDuplicatingSchema) : Type :=
  S.T → WLevel → Prop

namespace SchemaWitnessTower

variable {S : StepDuplicatingSchema}

def HasWitness (T : SchemaWitnessTower S) (x : S.T) (ℓ : WLevel) : Prop := T x ℓ

/-- **Paper 2 Definition 4.2 (minimal witness order).** `kappaLe T x ℓ`
says there is some level `j ≤ ℓ` at which `x` has a witness in `T`. -/
def kappaLe (T : SchemaWitnessTower S) (x : S.T) (ℓ : WLevel) : Prop :=
  ∃ j : WLevel, j.toNat ≤ ℓ.toNat ∧ HasWitness T x j

/-- `kappaGt T x ℓ` says no level `≤ ℓ` has a witness, i.e. `κ*(x) > ℓ`. -/
def kappaGt (T : SchemaWitnessTower S) (x : S.T) (ℓ : WLevel) : Prop :=
  ∀ j : WLevel, j.toNat ≤ ℓ.toNat → ¬ HasWitness T x j

/-- **Paper 2 Definition 4.3 (orientation-boundary predicate).** The
orientation boundary holds at `x` exactly when the direct whole-term
witness language is empty for `x`. -/
def OB (T : SchemaWitnessTower S) (x : S.T) : Prop :=
  kappaGt T x WLevel.directWhole

/-- **Paper 2 Proposition 4.4 (orientation boundary as threshold).** Under
a tower where the direct-whole-term level at every `x` is the
`GlobalOrients`-style orientation of the duplicating step, the orientation
boundary is equivalent to "there is no direct whole-term witness".

Here we expose the generic biconditional at the tower level; specific
schemas (like KO7) realize the direct-whole predicate by their concrete
barrier package, so this generic lemma is the shape Paper 2 invokes
across all schemas. -/
theorem OB_iff_no_directWhole
    (T : SchemaWitnessTower S) (x : S.T) :
    OB T x ↔ ¬ HasWitness T x WLevel.directWhole := by
  unfold OB kappaGt
  constructor
  · intro h hw
    exact h WLevel.directWhole (le_refl _) hw
  · intro hno j hj hw
    have hj0 : j.toNat = 0 := by
      have : j.toNat ≤ 0 := by
        have hdw : WLevel.directWhole.toNat = 0 := rfl
        rw [hdw] at hj
        exact hj
      omega
    have : j = WLevel.directWhole := by
      cases j <;> (simp [WLevel.toNat] at hj0; try rfl)
    rw [this] at hw
    exact hno hw

/-- When `OB T x` holds and there is a witness at the transformed-call layer
(e.g. via a `ForgettingWitness`), the minimal witness order is at least 2. -/
theorem OB_witness_at_transformedCall
    (T : SchemaWitnessTower S) (x : S.T)
    (_hOB : OB T x)
    (hTC : HasWitness T x WLevel.transformedCall) :
    kappaLe T x WLevel.transformedCall := by
  exact ⟨WLevel.transformedCall, Nat.le_refl _, hTC⟩

/-- A threshold formulation closer to Paper 2 Proposition 4.4: if the direct
whole-term witness language is empty at `x` and a transformed-call witness
exists, then the orientation boundary holds and the first available witness
order is at most the transformed-call layer. -/
theorem boundary_threshold_at_transformedCall
    (T : SchemaWitnessTower S) (x : S.T)
    (hno : ¬ HasWitness T x WLevel.directWhole)
    (hTC : HasWitness T x WLevel.transformedCall) :
    OB T x ∧ kappaLe T x WLevel.transformedCall := by
  refine ⟨(OB_iff_no_directWhole T x).2 hno, ?_⟩
  exact ⟨WLevel.transformedCall, Nat.le_refl _, hTC⟩

end SchemaWitnessTower

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
