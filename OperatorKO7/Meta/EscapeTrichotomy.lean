import OperatorKO7.Meta.PumpedBarrierClasses
import OperatorKO7.Meta.DepthBarrier
import OperatorKO7.Meta.PrecedenceBarrier
import OperatorKO7.Meta.MatrixBarrierLexD
import OperatorKO7.Meta.MatrixBarrierLexPermD

/-!
# Escape Trichotomy

This module replaces the paper's purely rhetorical "escape trichotomy" question
with a theorem for an explicit universe of Nat-valued direct orienters.

The theorem universe is intentionally narrow and reviewable:
- additive compositional measures
- transparent compositional measures
- pumped affine constructor-local measures
- pumped restricted-quadratic constructor-local measures
- pumped bounded-cross-term constructor-local measures
- pumped bounded-multilinear constructor-local measures
- pumped generalized bounded-polynomial constructor-local measures
- pumped max-plus constructor-local measures
- KO7-specific max-depth families
- KO7-specific pure head-precedence families
- tracked-primary componentwise pair families
- tracked-primary lexicographic pair families
- arbitrary finite tracked-primary lexicographic vector families
- permutation-priority finite tracked-primary lexicographic vector families

Within this universe, any successful root-step orienter must fail at least one of:
- wrapper-subterm sensitivity
- base-level successor transparency
- representability by the formalized Nat-valued direct families above

Dependency-pair frameworks and path orders remain outside this theorem universe.
Broader projection-based matrix extensions are handled later in this file through
their scalar representability layer rather than by these base constructors alone.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-- Wrapper-subterm sensitivity for a Nat-valued direct orienter:
both wrapper arguments must be strictly below the wrapped result. -/
def WrapSubtermSensitive (S : StepDuplicatingSchema) (μ : S.T → Nat) : Prop :=
  ∀ x y, μ x < μ (S.wrap x y) ∧ μ y < μ (S.wrap x y)

/-- Base-level successor transparency for a Nat-valued direct orienter. -/
def TransparentAtBase (S : StepDuplicatingSchema) (μ : S.T → Nat) : Prop :=
  μ (S.succ S.base) = μ S.base

/-- The explicit Nat-valued direct universe covered by the current barrier stack. -/
inductive NatDirectBarrierRepresentable (S : StepDuplicatingSchema) (μ : S.T → Nat) : Prop
  | additive (M : AdditiveMeasure S) (heval : M.eval = μ)
  | compositionalTransparent (CM : CompositionalMeasure S)
      (htransparent : CM.c_succ CM.c_base = CM.c_base) (heval : CM.eval = μ)
  | affineWithPump (M : AffineMeasureWithPump S) (heval : M.eval = μ)
  | quadraticWithPump (M : QuadraticCounterMeasureWithPump S) (heval : M.eval = μ)
  | crossQuadraticWithPump (M : CrossTermQuadraticMeasureWithPump S) (heval : M.eval = μ)
  | multilinearWithPump (M : MultilinearMeasureWithPump S) (heval : M.eval = μ)
  | polynomialWithPump (M : PolynomialMeasureWithPump S) (heval : M.eval = μ)
  | maxWithPump (M : MaxMeasureWithPump S) (heval : M.eval = μ)

/-- Escape trichotomy for the explicit Nat-valued direct universe:
any successful orienter must fail wrapper sensitivity, fail base-level transparency,
or fail representability by the formalized Nat-valued direct barrier families. -/
theorem nat_direct_escape_trichotomy
    {Sys : StepDuplicatingSystem} {μ : Sys.T → Nat}
    (horient : GlobalOrients Sys μ (· < ·)) :
    ¬ WrapSubtermSensitive Sys.toStepDuplicatingSchema μ ∨
      ¬ TransparentAtBase Sys.toStepDuplicatingSchema μ ∨
      ¬ NatDirectBarrierRepresentable Sys.toStepDuplicatingSchema μ := by
  classical
  by_cases hsub : WrapSubtermSensitive Sys.toStepDuplicatingSchema μ
  · by_cases htrans : TransparentAtBase Sys.toStepDuplicatingSchema μ
    · right
      right
      intro hrepr
      cases hrepr with
      | additive M heval =>
          subst heval
          exact (no_global_orients_additive (Sys := Sys) M) horient
      | compositionalTransparent CM htransparent heval =>
          subst heval
          exact (no_global_orients_compositional_transparent_succ
            (Sys := Sys) CM htransparent) horient
      | affineWithPump M heval =>
          subst heval
          exact (no_global_orients_affine_with_pump (Sys := Sys) M) horient
      | quadraticWithPump M heval =>
          subst heval
          exact (no_global_orients_quadratic_with_pump (Sys := Sys) M) horient
      | crossQuadraticWithPump M heval =>
          subst heval
          exact (no_global_orients_cross_quadratic_with_pump (Sys := Sys) M) horient
      | multilinearWithPump M heval =>
          subst heval
          exact (no_global_orients_multilinear_with_pump (Sys := Sys) M) horient
      | polynomialWithPump M heval =>
          subst heval
          exact (no_global_orients_polynomial_with_pump (Sys := Sys) M) horient
      | maxWithPump M heval =>
          subst heval
          exact (no_global_orients_max_with_pump (Sys := Sys) M) horient
    · right
      left
      exact htrans
  · left
    exact hsub

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating

namespace OperatorKO7.EscapeTrichotomy

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.MetaConjectureBoundary
open OperatorKO7.DepthBarrier
open OperatorKO7.PrecedenceBarrier

/-- An explicit KO7 direct-orienter universe covering the current scalar families and the
tracked-primary pair families. -/
inductive KO7DirectOrienter where
  | nat (μ : Trace → Nat)
  | pairComponentwise (μ : Trace → StepDuplicatingSchema.Vec2)
  | pairLex (μ : Trace → StepDuplicatingSchema.Vec2)
  | vecLex (d : Nat) (μ : Trace → Fin (d + 1) → Nat)
  | vecPermLex (d : Nat) (σ : Equiv.Perm (Fin (d + 1))) (μ : Trace → Fin (d + 1) → Nat)

/-- The tracked primary scalar exposed by an orienter in the explicit KO7 direct universe. -/
def KO7DirectOrienter.primaryScalar : KO7DirectOrienter → Trace → Nat
  | .nat μ => μ
  | .pairComponentwise μ => fun t => (μ t).1
  | .pairLex μ => fun t => (μ t).1
  | .vecLex d μ => fun t => μ t (StepDuplicatingSchema.primaryIdx d)
  | .vecPermLex d σ μ => fun t => μ t (StepDuplicatingSchema.permPrimaryIdx σ)

/-- Orientation predicate for the explicit KO7 direct-orienter universe. -/
def KO7DirectOrienter.Orients : KO7DirectOrienter → Prop
  | .nat μ =>
      MetaConjectureBoundary.GlobalOrients μ (· < ·)
  | .pairComponentwise μ =>
      StepDuplicatingSchema.GlobalOrients ko7System μ StepDuplicatingSchema.PairLt
  | .pairLex μ =>
      StepDuplicatingSchema.GlobalOrients ko7System μ StepDuplicatingSchema.PairLexLt
  | .vecLex _ μ =>
      StepDuplicatingSchema.GlobalOrients ko7System μ StepDuplicatingSchema.VecLexLt
  | .vecPermLex _ σ μ =>
      StepDuplicatingSchema.GlobalOrients ko7System μ (StepDuplicatingSchema.VecPermLexLt σ)

/-- KO7-specific extension of the Nat-valued direct universe used by the escape
trichotomy theorem. It adds the theorem-level depth and pure-precedence families
to the generic additive / transparent-compositional / pumped affine / pumped
restricted-quadratic families. -/
inductive KO7NatDirectBarrierRepresentable (μ : Trace → Nat) : Prop
  | additive (M : AdditiveCompositionalMeasure) (heval : M.eval = μ)
  | compositionalTransparent (CM : CompositionalMeasure)
      (htransparent : CM.c_delta CM.c_void = CM.c_void) (heval : CM.eval = μ)
  | affineWithPump (M : StepDuplicatingSchema.AffineMeasureWithPump ko7Schema)
      (heval : ∀ t : Trace, M.eval t = μ t)
  | quadraticWithPump (M : StepDuplicatingSchema.QuadraticCounterMeasureWithPump ko7Schema)
      (heval : ∀ t : Trace, M.eval t = μ t)
  | crossQuadraticWithPump
      (M : StepDuplicatingSchema.CrossTermQuadraticMeasureWithPump ko7Schema)
      (heval : ∀ t : Trace, M.eval t = μ t)
  | multilinearWithPump
      (M : StepDuplicatingSchema.MultilinearMeasureWithPump ko7Schema)
      (heval : ∀ t : Trace, M.eval t = μ t)
  | polynomialWithPump
      (M : StepDuplicatingSchema.PolynomialMeasureWithPump ko7Schema)
      (heval : ∀ t : Trace, M.eval t = μ t)
  | maxWithPump
      (M : StepDuplicatingSchema.MaxMeasureWithPump ko7Schema)
      (heval : ∀ t : Trace, M.eval t = μ t)
  | depth (M : MaxDepthMeasure) (heval : M.eval = μ)
  | precedence (M : HeadPrecedenceFamily) (heval : M.eval = μ)

/-- Extended KO7 direct universe adding the tracked-primary pair families to the previous
Nat-valued direct families. -/
inductive KO7DirectBarrierRepresentable : KO7DirectOrienter → Prop
  | additive (M : AdditiveCompositionalMeasure) :
      KO7DirectBarrierRepresentable (.nat M.eval)
  | compositionalTransparent (CM : CompositionalMeasure)
      (htransparent : CM.c_delta CM.c_void = CM.c_void) :
      KO7DirectBarrierRepresentable (.nat CM.eval)
  | affineWithPump (M : StepDuplicatingSchema.AffineMeasureWithPump ko7Schema) :
      KO7DirectBarrierRepresentable (.nat M.eval)
  | quadraticWithPump (M : StepDuplicatingSchema.QuadraticCounterMeasureWithPump ko7Schema) :
      KO7DirectBarrierRepresentable (.nat M.eval)
  | crossQuadraticWithPump
      (M : StepDuplicatingSchema.CrossTermQuadraticMeasureWithPump ko7Schema) :
      KO7DirectBarrierRepresentable (.nat M.eval)
  | multilinearWithPump
      (M : StepDuplicatingSchema.MultilinearMeasureWithPump ko7Schema) :
      KO7DirectBarrierRepresentable (.nat M.eval)
  | polynomialWithPump
      (M : StepDuplicatingSchema.PolynomialMeasureWithPump ko7Schema) :
      KO7DirectBarrierRepresentable (.nat M.eval)
  | maxWithPump
      (M : StepDuplicatingSchema.MaxMeasureWithPump ko7Schema) :
      KO7DirectBarrierRepresentable (.nat M.eval)
  | depth (M : MaxDepthMeasure) :
      KO7DirectBarrierRepresentable (.nat M.eval)
  | precedence (M : HeadPrecedenceFamily) :
      KO7DirectBarrierRepresentable (.nat M.eval)
  | matrix2ComponentwiseWithPrimaryPump
      (M : StepDuplicatingSchema.MatrixMeasure2WithPrimaryPump ko7Schema) :
      KO7DirectBarrierRepresentable (.pairComponentwise M.eval)
  | matrix2LexWithPrimaryPump
      (M : StepDuplicatingSchema.MatrixMeasure2WithPrimaryPump ko7Schema) :
      KO7DirectBarrierRepresentable (.pairLex M.eval)
  | matrixLexDWithPrimaryPump
      {d : Nat}
      (M : StepDuplicatingSchema.MatrixLexMeasureDWithPrimaryPump ko7Schema d) :
      KO7DirectBarrierRepresentable (.vecLex d M.eval)
  | matrixLexPermWithPrimaryPump
      {d : Nat}
      (M : StepDuplicatingSchema.MatrixLexPermMeasureDWithPrimaryPump ko7Schema d) :
      KO7DirectBarrierRepresentable (.vecPermLex d M.priority M.eval)

/-- KO7 escape trichotomy for the explicit Nat-valued direct universe formalized
in the artifact. Any successful Nat-valued root-step orienter must fail wrapper
subterm sensitivity, fail base-level successor transparency, or fall outside the
formalized Nat-valued direct barrier families. -/
theorem ko7_nat_direct_escape_trichotomy
    {μ : Trace → Nat}
    (horient : MetaConjectureBoundary.GlobalOrients μ (· < ·)) :
    ¬ StepDuplicatingSchema.WrapSubtermSensitive ko7Schema μ ∨
      ¬ StepDuplicatingSchema.TransparentAtBase ko7Schema μ ∨
      ¬ KO7NatDirectBarrierRepresentable μ := by
  classical
  by_cases hsub : StepDuplicatingSchema.WrapSubtermSensitive ko7Schema μ
  · by_cases htrans : StepDuplicatingSchema.TransparentAtBase ko7Schema μ
    · right
      right
      intro hrepr
      cases hrepr with
      | additive M heval =>
          subst heval
          exact (no_global_step_orientation_additive_compositional M) horient
      | compositionalTransparent CM htransparent heval =>
          subst heval
          exact (no_global_step_orientation_compositional_transparent_delta CM htransparent) horient
      | affineWithPump M heval =>
          have hrepr :
              M.eval = μ := by
            funext t
            exact heval t
          subst hrepr
          exact (PumpedBarrierClasses.no_global_step_orientation_affine_with_pump M) horient
      | quadraticWithPump M heval =>
          have hrepr :
              M.eval = μ := by
            funext t
            exact heval t
          subst hrepr
          exact (PumpedBarrierClasses.no_global_step_orientation_quadratic_with_pump M) horient
      | crossQuadraticWithPump M heval =>
          have hrepr :
              M.eval = μ := by
            funext t
            exact heval t
          subst hrepr
          exact (PumpedBarrierClasses.no_global_step_orientation_cross_quadratic_with_pump M) horient
      | multilinearWithPump M heval =>
          have hrepr :
              M.eval = μ := by
            funext t
            exact heval t
          subst hrepr
          exact (PumpedBarrierClasses.no_global_step_orientation_multilinear_with_pump M) horient
      | polynomialWithPump M heval =>
          have hrepr :
              M.eval = μ := by
            funext t
            exact heval t
          subst hrepr
          exact (PumpedBarrierClasses.no_global_step_orientation_polynomial_with_pump M) horient
      | maxWithPump M heval =>
          have hrepr :
              M.eval = μ := by
            funext t
            exact heval t
          subst hrepr
          exact (PumpedBarrierClasses.no_global_step_orientation_max_with_pump M) horient
      | depth M heval =>
          subst heval
          exact (no_global_step_orientation_maxDepth M) horient
      | precedence M heval =>
          subst heval
          exact (no_global_step_orientation_headPrecedenceFamily M) horient
    · right
      left
      exact htrans
  · left
    exact hsub

/-- Extended KO7 escape trichotomy for the explicit direct universe formalized in the
artifact, now including the tracked-primary componentwise and lexicographic pair families.
The failure modes are stated on the tracked primary scalar exposed by the orienter. -/
theorem ko7_direct_escape_trichotomy_extended
    {O : KO7DirectOrienter}
    (horient : O.Orients) :
    ¬ StepDuplicatingSchema.WrapSubtermSensitive ko7Schema O.primaryScalar ∨
      ¬ StepDuplicatingSchema.TransparentAtBase ko7Schema O.primaryScalar ∨
      ¬ KO7DirectBarrierRepresentable O := by
  classical
  by_cases hsub : StepDuplicatingSchema.WrapSubtermSensitive ko7Schema O.primaryScalar
  · by_cases htrans : StepDuplicatingSchema.TransparentAtBase ko7Schema O.primaryScalar
    · right
      right
      intro hrepr
      cases hrepr with
      | additive M =>
          exact (no_global_step_orientation_additive_compositional M) horient
      | compositionalTransparent CM htransparent =>
          exact
            (no_global_step_orientation_compositional_transparent_delta CM htransparent) horient
      | affineWithPump M =>
          exact (PumpedBarrierClasses.no_global_step_orientation_affine_with_pump M) horient
      | quadraticWithPump M =>
          exact (PumpedBarrierClasses.no_global_step_orientation_quadratic_with_pump M) horient
      | crossQuadraticWithPump M =>
          exact (PumpedBarrierClasses.no_global_step_orientation_cross_quadratic_with_pump M) horient
      | multilinearWithPump M =>
          exact (PumpedBarrierClasses.no_global_step_orientation_multilinear_with_pump M) horient
      | polynomialWithPump M =>
          exact (PumpedBarrierClasses.no_global_step_orientation_polynomial_with_pump M) horient
      | maxWithPump M =>
          exact (PumpedBarrierClasses.no_global_step_orientation_max_with_pump M) horient
      | depth M =>
          exact (no_global_step_orientation_maxDepth M) horient
      | precedence M =>
          exact (no_global_step_orientation_headPrecedenceFamily M) horient
      | matrix2ComponentwiseWithPrimaryPump M =>
          exact (PumpedBarrierClasses.no_global_step_orientation_matrix2_with_primary_pump M) horient
      | matrix2LexWithPrimaryPump M =>
          exact (PumpedBarrierClasses.no_global_step_orientation_matrix2_lex_with_primary_pump M) horient
      | matrixLexDWithPrimaryPump M =>
          exact (OperatorKO7.MatrixBarrierLexD.no_global_step_orientation_matrixLexD_with_primary_pump M) horient
      | matrixLexPermWithPrimaryPump M =>
          exact (OperatorKO7.MatrixBarrierLexPermD.no_global_step_orientation_matrixLexPermD_with_primary_pump M) horient
    · right
      left
      exact htrans
  · left
    exact hsub

/-- Broader projection-based representability layer for direct componentwise orienters:
if a fixed scalar projection is forced to decrease by the ambient order, and that scalar
already belongs to the explicit KO7 Nat-valued barrier universe, then the same escape
trichotomy applies to the projected primary scalar. -/
structure KO7ProjectionBarrierRepresentable
    {α : Type} (μ : Trace → α) (R : α → α → Prop) (π : α → Nat) : Prop where
  projection_strict : ∀ {u v : α}, R u v → π u < π v
  represented : KO7NatDirectBarrierRepresentable (fun t => π (μ t))

/-- Projection-based extension of the KO7 escape trichotomy. -/
theorem ko7_projection_escape_trichotomy
    {α : Type} {μ : Trace → α} {R : α → α → Prop} {π : α → Nat}
    (horient : StepDuplicatingSchema.GlobalOrients ko7System μ R) :
    ¬ StepDuplicatingSchema.WrapSubtermSensitive ko7Schema (fun t => π (μ t)) ∨
      ¬ StepDuplicatingSchema.TransparentAtBase ko7Schema (fun t => π (μ t)) ∨
      ¬ KO7ProjectionBarrierRepresentable μ R π := by
  classical
  by_cases hsub : StepDuplicatingSchema.WrapSubtermSensitive ko7Schema (fun t => π (μ t))
  · by_cases htrans : StepDuplicatingSchema.TransparentAtBase ko7Schema (fun t => π (μ t))
    · right
      right
      intro hrepr
      have hscalar : StepDuplicatingSchema.GlobalOrients ko7System (fun t => π (μ t)) (· < ·) := by
        intro a b hab
        exact hrepr.projection_strict (horient hab)
      have htri := ko7_nat_direct_escape_trichotomy (μ := fun t => π (μ t)) hscalar
      cases htri with
      | inl hbad =>
          exact hbad hsub
      | inr hrest =>
          cases hrest with
          | inl hbad =>
              exact hbad htrans
          | inr hbad =>
              exact hbad hrepr.represented
    · right
      left
      exact htrans
  · left
    exact hsub

/-- Weighted functional matrix families enter the extended trichotomy through their
projected scalar affine-with-pump witness. -/
theorem matrixFunctional_projection_representable
    {d : Nat}
    (M : StepDuplicatingSchema.MatrixFunctionalMeasureWithProjectedAffinePump ko7Schema d) :
    KO7ProjectionBarrierRepresentable
      M.eval StepDuplicatingSchema.VecLt
      (fun v => StepDuplicatingSchema.weightedSum M.weight v) := by
  refine ⟨?_, ?_⟩
  · intro u v h
    exact StepDuplicatingSchema.weightedSum_lt_of_vecLt M.h_weight_support h
  · exact KO7NatDirectBarrierRepresentable.affineWithPump M.projectedAffineWithPump (by intro t; rfl)

/-- Balanced mixed-coordinate matrix families enter the extended trichotomy through the
aggregate coordinate-sum projection. -/
theorem matrixMix2_sum_projection_representable
    (M : StepDuplicatingSchema.MatrixMix2MeasureWithSumPump ko7Schema) :
    KO7ProjectionBarrierRepresentable
      M.eval StepDuplicatingSchema.PairLt StepDuplicatingSchema.vecSum := by
  refine ⟨?_, ?_⟩
  · intro u v h
    exact StepDuplicatingSchema.vecSum_lt_of_pairLt h
  · exact KO7NatDirectBarrierRepresentable.affineWithPump M.sumAffineWithPump (by intro t; rfl)

/-- Weighted functional matrix escape trichotomy corollary. -/
theorem ko7_matrixFunctional_escape_trichotomy
    {d : Nat}
    (M : StepDuplicatingSchema.MatrixFunctionalMeasureWithProjectedAffinePump ko7Schema d)
    (horient : StepDuplicatingSchema.GlobalOrients ko7System M.eval StepDuplicatingSchema.VecLt) :
    ¬ StepDuplicatingSchema.WrapSubtermSensitive ko7Schema
        (fun t => StepDuplicatingSchema.weightedSum M.weight (M.eval t)) ∨
      ¬ StepDuplicatingSchema.TransparentAtBase ko7Schema
        (fun t => StepDuplicatingSchema.weightedSum M.weight (M.eval t)) ∨
      False := by
  have htri :=
    ko7_projection_escape_trichotomy
      (μ := M.eval) (R := StepDuplicatingSchema.VecLt)
      (π := fun v => StepDuplicatingSchema.weightedSum M.weight v) horient
  cases htri with
  | inl hbad =>
      exact Or.inl hbad
  | inr hrest =>
      cases hrest with
      | inl hbad =>
          exact Or.inr (Or.inl hbad)
      | inr hbad =>
          exfalso
          exact hbad (matrixFunctional_projection_representable M)

/-- Balanced mixed-coordinate escape trichotomy corollary. -/
theorem ko7_matrixMix2_escape_trichotomy
    (M : StepDuplicatingSchema.MatrixMix2MeasureWithSumPump ko7Schema)
    (horient : StepDuplicatingSchema.GlobalOrients ko7System M.eval StepDuplicatingSchema.PairLt) :
    ¬ StepDuplicatingSchema.WrapSubtermSensitive ko7Schema
        (fun t => StepDuplicatingSchema.vecSum (M.eval t)) ∨
      ¬ StepDuplicatingSchema.TransparentAtBase ko7Schema
        (fun t => StepDuplicatingSchema.vecSum (M.eval t)) ∨
      False := by
  have htri :=
    ko7_projection_escape_trichotomy
      (μ := M.eval) (R := StepDuplicatingSchema.PairLt)
      (π := StepDuplicatingSchema.vecSum) horient
  cases htri with
  | inl hbad =>
      exact Or.inl hbad
  | inr hrest =>
      cases hrest with
      | inl hbad =>
          exact Or.inr (Or.inl hbad)
      | inr hbad =>
          exfalso
          exact hbad (matrixMix2_sum_projection_representable M)

end OperatorKO7.EscapeTrichotomy
