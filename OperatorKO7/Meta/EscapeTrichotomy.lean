import OperatorKO7.Meta.PumpedBarrierClasses
import OperatorKO7.Meta.DepthBarrier
import OperatorKO7.Meta.PrecedenceBarrier

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
- KO7-specific max-depth families
- KO7-specific pure head-precedence families

Within this universe, any successful root-step orienter must fail at least one of:
- wrapper-subterm sensitivity
- base-level successor transparency
- representability by the formalized Nat-valued direct families above

Pair-valued tracked barriers, dependency-pair frameworks, and path orders remain
outside this theorem universe.
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

/-- The tracked primary scalar exposed by an orienter in the explicit KO7 direct universe. -/
def KO7DirectOrienter.primaryScalar : KO7DirectOrienter → Trace → Nat
  | .nat μ => μ
  | .pairComponentwise μ => fun t => (μ t).1
  | .pairLex μ => fun t => (μ t).1

/-- Orientation predicate for the explicit KO7 direct-orienter universe. -/
def KO7DirectOrienter.Orients : KO7DirectOrienter → Prop
  | .nat μ =>
      MetaConjectureBoundary.GlobalOrients μ (· < ·)
  | .pairComponentwise μ =>
      StepDuplicatingSchema.GlobalOrients ko7System μ StepDuplicatingSchema.PairLt
  | .pairLex μ =>
      StepDuplicatingSchema.GlobalOrients ko7System μ StepDuplicatingSchema.PairLexLt

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
      | depth M =>
          exact (no_global_step_orientation_maxDepth M) horient
      | precedence M =>
          exact (no_global_step_orientation_headPrecedenceFamily M) horient
      | matrix2ComponentwiseWithPrimaryPump M =>
          exact (PumpedBarrierClasses.no_global_step_orientation_matrix2_with_primary_pump M) horient
      | matrix2LexWithPrimaryPump M =>
          exact (PumpedBarrierClasses.no_global_step_orientation_matrix2_lex_with_primary_pump M) horient
    · right
      left
      exact htrans
  · left
    exact hsub

end OperatorKO7.EscapeTrichotomy
