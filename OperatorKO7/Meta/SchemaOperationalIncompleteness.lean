import OperatorKO7.Meta.SchemaForgettingWitness

/-!
# Schema-Generic Operational Incompleteness

Schema-level mechanization of Paper 2 Definitions 5.1, 5.8, 5.9, 5.16 and
Propositions 5.2, 5.3, 5.10, 5.17.

This module lifts the KO7-specific `PayloadOperationalIncompleteness` from
[`Meta/OperationalIncompleteness.lean`](OperationalIncompleteness.lean) to a
schema-generic interface that applies to any step-duplicating schema. It
also packages the construction-vs-confession asymmetry and the
projection-transaction reading of the orientation boundary.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-! ## Def 5.1 abstract operational incompleteness -/

/-- An abstract proof-language interface for a fixed operational question. -/
structure OperationalQuestion (Statement : Type) where
  derivable : Statement → Prop
  dependsOnDimension : Statement → Prop
  constrainsTarget : Statement → Prop
  dimensionPresent : Prop

/-- **Paper 2 Definition 5.1 (abstract form).** A proof language is
operationally incomplete at a chosen dimension when that dimension is present,
but no derivable statement both depends on it and constrains the target
question. -/
def OperationallyIncomplete {Statement : Type}
    (Q : OperationalQuestion Statement) : Prop :=
  Q.dimensionPresent
    ∧ ∀ ψ, Q.derivable ψ →
        ¬ (Q.dependsOnDimension ψ ∧ Q.constrainsTarget ψ)

/-- Direct whole-term witness claims in the direct-aggregation language. -/
inductive DirectAggregationClaim (Sys : StepDuplicatingSystem) where
  | additive
      (M : AdditiveMeasure Sys.toStepDuplicatingSchema)
  | compositional
      (CM : CompositionalMeasure Sys.toStepDuplicatingSchema)
      (htrans : CM.c_succ CM.c_base = CM.c_base)
  | affine
      (M : AffineMeasure Sys.toStepDuplicatingSchema)
      (hunb : HasUnboundedRange M)

/-- A claim is derivable in the direct-aggregation language exactly when the
corresponding direct witness globally orients the system. -/
def DirectAggregationClaim.derivable
    {Sys : StepDuplicatingSystem} :
    DirectAggregationClaim Sys → Prop
  | .additive M => GlobalOrients Sys M.eval (· < ·)
  | .compositional CM _ => GlobalOrients Sys CM.eval (· < ·)
  | .affine M _ => GlobalOrients Sys M.eval (· < ·)

/-- In the canonical direct-aggregation language, every witness claim is a
dimension-using attempt: it is supposed to derive termination by a direct
whole-term account of the input. -/
def DirectAggregationClaim.dependsOnDimension
    {Sys : StepDuplicatingSystem} :
    DirectAggregationClaim Sys → Prop :=
  fun _ => True

/-- Any successful direct-aggregation witness would constrain the target
termination question by construction. -/
def DirectAggregationClaim.constrainsTarget
    {Sys : StepDuplicatingSystem} :
    DirectAggregationClaim Sys → Prop :=
  fun _ => True

/-- The canonical operational question attached to the direct-aggregation
language for a fixed step-duplicating system. -/
def directAggregationQuestion
    (Sys : StepDuplicatingSystem) (dimensionPresent : Prop) :
    OperationalQuestion (DirectAggregationClaim Sys) where
  derivable := DirectAggregationClaim.derivable
  dependsOnDimension := DirectAggregationClaim.dependsOnDimension
  constrainsTarget := DirectAggregationClaim.constrainsTarget
  dimensionPresent := dimensionPresent

/-- **Paper 2 Theorem 5.2 (abstract canonical instance).** Once the chosen
dimension is present, the direct-aggregation language is operationally
incomplete: every direct witness claim is blocked by the schema barriers, so no
derivable claim both depends on the dimension and constrains termination. -/
theorem directAggregationQuestion_operationallyIncomplete
    {Sys : StepDuplicatingSystem} {dimensionPresent : Prop}
    (hpresent : dimensionPresent) :
    OperationallyIncomplete (directAggregationQuestion Sys dimensionPresent) := by
  refine ⟨hpresent, ?_⟩
  intro ψ hψ
  cases ψ with
  | additive M =>
      intro hpair
      exact no_global_orients_additive (Sys := Sys) M hψ
  | compositional CM htrans =>
      intro hpair
      exact no_global_orients_compositional_transparent_succ (Sys := Sys) CM htrans hψ
  | affine M hunb =>
      intro hpair
      exact no_global_orients_affine_of_unbounded (Sys := Sys) M hunb hψ

/-! ## Concrete schema evidence bundle -/

/-- **Paper 2 Definition 5.1 (operational incompleteness).** A
step-duplicating system is *operationally incomplete at dimension π for
a target property* when no direct additive measure on the schema both
respects the dimension (via wrapper-subterm sensitivity) and orients the
duplicating rule globally.

The dimension `π` is modelled abstractly as a predicate on the schema's
carrier; Paper 2's canonical instance is `π_y` (the step-argument slot),
which we recover as a KO7 specialization in the companion file. -/
structure OperationalIncompleteness (Sys : StepDuplicatingSystem) where
  noAdditiveOrienter :
    ∀ (M : AdditiveMeasure Sys.toStepDuplicatingSchema),
      ¬ GlobalOrients Sys M.eval (· < ·)
  noCompositionalOrienter :
    ∀ (CM : CompositionalMeasure Sys.toStepDuplicatingSchema),
      CM.c_succ CM.c_base = CM.c_base →
        ¬ GlobalOrients Sys CM.eval (· < ·)
  noAffineOrienter :
    ∀ (M : AffineMeasure Sys.toStepDuplicatingSchema),
      HasUnboundedRange M →
        ¬ GlobalOrients Sys M.eval (· < ·)
  forgettingWitness : ForgettingWitness Sys.toStepDuplicatingSchema

/-- **Paper 2 Theorem 5.2 (canonical instance).** Every step-duplicating
system equipped with a `ProjectionRank` exhibits schema-level operational
incompleteness: the schema's additive, transparent-compositional, and
affine-with-pump direct barriers already fail, while the projection rank
yields a forgetting witness. -/
def OperationalIncompleteness.ofProjectionRank
    {Sys : StepDuplicatingSystem}
    (R : ProjectionRank Sys.toStepDuplicatingSchema) :
    OperationalIncompleteness Sys where
  noAdditiveOrienter := fun M => no_global_orients_additive (Sys := Sys) M
  noCompositionalOrienter := fun CM htrans =>
    no_global_orients_compositional_transparent_succ
      (Sys := Sys) CM htrans
  noAffineOrienter := fun M hunb =>
    no_global_orients_affine_of_unbounded (Sys := Sys) M hunb
  forgettingWitness := ForgettingWitness.ofProjectionRank R

/-- **Paper 2 Corollary 5.3 (universality).** Schema-level operational
incompleteness is universal: it depends only on `Sys` having a projection
rank, not on any KO7-specific structure. -/
theorem operationalIncompleteness_universal
    {Sys : StepDuplicatingSystem}
    (R : ProjectionRank Sys.toStepDuplicatingSchema) :
    ∃ _ : OperationalIncompleteness Sys, True :=
  ⟨OperationalIncompleteness.ofProjectionRank R, trivial⟩

/-- The abstract operational-incompleteness predicate and the concrete schema
evidence bundle are both available uniformly from the same projection-rank
input. -/
theorem canonical_operational_instance
    {Sys : StepDuplicatingSystem} {dimensionPresent : Prop}
    (hpresent : dimensionPresent)
    (R : ProjectionRank Sys.toStepDuplicatingSchema) :
    OperationallyIncomplete (directAggregationQuestion Sys dimensionPresent)
      ∧ Nonempty (OperationalIncompleteness Sys) := by
  exact ⟨directAggregationQuestion_operationallyIncomplete hpresent,
    ⟨OperationalIncompleteness.ofProjectionRank R⟩⟩

/-! ## Def 5.8, 5.9 construction vs confession -/

/-- **Paper 2 Definition 5.9 (confession method).** A termination method is
a *confession* when it factors through a forgetting witness, i.e. it
succeeds by projecting away the payload dimension under external
soundness license. -/
structure ConfessionResponse (S : StepDuplicatingSchema) where
  forgetting : ForgettingWitness S

/-- **Paper 2 Definition 5.8 (construction method).** A termination method is
a *construction* when its rank is not a forgetting witness — concretely,
when it preserves wrapper sensitivity on both payload positions. Paper 2's
examples are nonlinear polynomial interpretations and MPO path orders. -/
structure ConstructionResponse (S : StepDuplicatingSchema) where
  rank : S.T → Nat
  orientsDupStep :
    ∀ b s n,
      rank (S.wrap s (S.recur b s n))
        < rank (S.recur b s (S.succ n))
  wrapperSensitiveLeft :
    ∀ x y : S.T, rank (S.wrap x y) > rank x
  wrapperSensitiveRight :
    ∀ x y : S.T, rank (S.wrap x y) > rank y

/-- **Paper 2 Proposition 5.10 (construction vs confession asymmetry).** No
response can simultaneously be a construction and (via its rank) a
forgetting witness: the wrapper-sensitivity clauses of a construction
contradict the wrapper-sensitivity-violation clauses of a forgetting
witness. -/
theorem construction_confession_exclusive
    {S : StepDuplicatingSchema}
    (C : ConstructionResponse S)
    (F : ForgettingWitness S)
    (hrank : C.rank = F.rank) :
    False := by
  obtain ⟨x, y, hviol⟩ := F.violatesPayloadLeft
  have hsens : C.rank (S.wrap x y) > C.rank x := C.wrapperSensitiveLeft x y
  rw [hrank] at hsens
  exact hviol hsens

/-! ## Def 5.16, Prop 5.17 projection-transaction reading -/

/-- **Paper 2 Definition 5.16 (orientation boundary as projection-transaction).**
The boundary is a static map from the generative trace through a named
dimension under an external license to the verdict space. At the schema
level, the projection-transaction is captured by the existence of a
forgetting witness. -/
structure ProjectionTransaction (S : StepDuplicatingSchema) where
  dimension : S.T → Nat
  license : Prop
  boundary : ForgettingWitness S
  /-- The license is the external schematic annotation that justifies
  forgetting the wrapper context. At this abstraction level we record its
  propositional placeholder; concrete instances discharge it by the
  Arts–Giesl soundness theorem (or analogues for SCT / counter-projection
  / argument filtering). -/
  licensed : license

/-- A step-indexed family of projection transactions is static when the
dimension, license, and forgetting witness do not vary with the trace stage. -/
def IsStaticProjectionFamily {S : StepDuplicatingSchema}
    (τ : Nat → ProjectionTransaction S) : Prop :=
  ∀ i,
    (τ i).dimension = (τ 0).dimension
      ∧ (τ i).license = (τ 0).license
      ∧ (τ i).boundary = (τ 0).boundary

/-- **Paper 2 Proposition 5.17 (boundary is static, not dynamic).** The
projection-transaction depends only on the triple (`dimension`, `license`,
`boundary`) and *not* on any per-step state of the generative trace. This
is captured by the fact that the constant step-indexed family generated by a
single `ProjectionTransaction` is static in the above sense. -/
theorem projection_transaction_static
    {S : StepDuplicatingSchema} (T : ProjectionTransaction S) :
    IsStaticProjectionFamily (fun _ => T) := by
  intro i
  exact ⟨rfl, rfl, rfl⟩

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
