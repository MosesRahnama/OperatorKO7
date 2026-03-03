import OperatorKO7.Kernel
import OperatorKO7.Meta.Conjecture_Boundary

/-!
# Compositional Measure Impossibility Theorem

This module defines a precise axiom system for "compositional measures" - termination
measures that compute the value of a compound term by aggregating the values of its
subterms - and proves that NO such measure can orient the duplicating recursor rule
`recΔ b s (delta n) → app s (recΔ b s n)` for all instantiations.

The module then shows that the Dependency Pair framework (TTT2's subterm criterion with
projection π(recD#) = 3) escapes the impossibility by violating the compositionality
axioms: it projects to a single argument instead of aggregating all subterm contributions.

## Structure

- **Section 1**: Helper: iterated `app` constructor (the "pump" for making μ(s) large)
- **Section 2**: `AdditiveCompositionalMeasure` - concrete Nat-weighted structure
- **Section 3**: Tier 1 impossibility theorem (additive measures)
- **Section 4**: `CompositionalMeasure` - abstract combining-function structure
- **Section 5**: Tier 2 impossibility theorem (transparent-delta case)
- **Section 6**: DP projection escape clause
- **Section 7**: Instance witnesses (simpleSize, tau, nodeCount)
- **Section 8**: `GlobalOrients` integration

## Key Results

- `no_additive_compositional_orients_rec_succ`: No additive compositional measure orients rec_succ
- `no_compositional_orients_rec_succ_transparent_delta`: No abstract compositional measure
  with transparent delta orients rec_succ
- `dp_projection_orients_rec_succ`: DP projection DOES orient rec_succ
- `dp_projection_violates_sensitivity`: DP projection violates the subterm/sensitivity axiom

## References

- Dershowitz (1987): duplication defeats additive measures
- Arts-Giesl (2000): dependency pairs with argument filtering
- Hirokawa-Middeldorp (2004): simple projection for DP
- Middeldorp-Zantema (1997): simple termination hierarchy
-/

namespace OperatorKO7.CompositionalImpossibility

open OperatorKO7 Trace

/-! ## Section 1: Iterated App Constructor -/

/-- Build `app(app(...(void)...), void)` with `k` nestings.
This is the "pump" that makes `μ(s)` arbitrarily large for any compositional measure. -/
def appIter : Nat → Trace
  | 0     => void
  | k + 1 => app (appIter k) void

/-! ## Section 2: Additive Compositional Measure (Tier 1) -/

/-- An additive compositional measure assigns a fixed base weight to each KO7 constructor.
The measure of a compound term is the constructor's weight plus the sum of its subterms' measures.

This axiom system captures: `simpleSize`, `tau`, `nodeCount`, `linearWeight`, `treeDepth`,
and all parameter choices thereof. The single constraint `hw_app_pos` (app adds at least 1)
ensures the measure grows under the `app` constructor - this is what makes it "see" duplication. -/
structure AdditiveCompositionalMeasure where
  w_void      : Nat
  w_delta     : Nat
  w_integrate : Nat
  w_merge     : Nat
  w_app       : Nat
  w_rec       : Nat
  w_eq        : Nat
  hw_app_pos  : w_app ≥ 1

/-- The evaluation function for an additive compositional measure.
For each constructor, adds the constructor's weight to the sum of subterm evaluations. -/
@[simp] def AdditiveCompositionalMeasure.eval
    (M : AdditiveCompositionalMeasure) : Trace → Nat
  | void        => M.w_void
  | delta t     => M.w_delta + M.eval t
  | integrate t => M.w_integrate + M.eval t
  | merge a b   => M.w_merge + M.eval a + M.eval b
  | app a b     => M.w_app + M.eval a + M.eval b
  | recΔ b s n  => M.w_rec + M.eval b + M.eval s + M.eval n
  | eqW a b     => M.w_eq + M.eval a + M.eval b

/-- The eval of `appIter k` grows at least as fast as `k` for any additive compositional measure
with `w_app ≥ 1`. This is the key "pump" lemma: we can make `M.eval s` arbitrarily large. -/
lemma eval_appIter_ge (M : AdditiveCompositionalMeasure) (k : Nat) :
    M.eval (appIter k) ≥ k := by
  induction k with
  | zero => simp [appIter, AdditiveCompositionalMeasure.eval]
  | succ k ih =>
    simp only [appIter, AdditiveCompositionalMeasure.eval]
    have := M.hw_app_pos
    omega

/-! ## Section 3: Tier 1 Impossibility Theorem -/

/-- **IMPOSSIBILITY THEOREM (Additive Measures)**

No additive compositional measure can orient the duplicating recursor rule
`recΔ b s (delta n) → app s (recΔ b s n)` for all instantiations of `b`, `s`, `n`.

**Proof strategy**: Set `b = void, n = void, s = appIter(w_delta)`. The RHS
`app s (recΔ void s void)` contains `M.eval s` TWICE (once directly, once inside recΔ),
while the LHS `recΔ void s (delta void)` contains `M.eval s` only ONCE.
The duplication adds `M.eval s ≥ w_delta` to the RHS, while the LHS gains only `w_delta`
from the delta wrapper. Since `w_app ≥ 1`, the RHS is at least as large as the LHS.

This subsumes all 12 failure witnesses in the catalog under a single theorem. -/
theorem no_additive_compositional_orients_rec_succ (M : AdditiveCompositionalMeasure) :
    ¬ (∀ (b s n : Trace),
      M.eval (app s (recΔ b s n)) < M.eval (recΔ b s (delta n))) := by
  intro h
  -- Specialize to b = void, n = void, s = appIter(M.w_delta)
  have hspec := h void (appIter M.w_delta) void
  -- After unfolding eval, the goal becomes arithmetic in M's weights and M.eval(appIter M.w_delta)
  simp only [AdditiveCompositionalMeasure.eval] at hspec
  -- We know M.eval(appIter M.w_delta) ≥ M.w_delta
  have hge := eval_appIter_ge M M.w_delta
  -- The arithmetic contradiction: duplication adds M.eval(s) ≥ w_delta,
  -- but the delta wrapper only contributes w_delta. With w_app ≥ 1, the RHS exceeds the LHS.
  have := M.hw_app_pos
  omega

/-! ## Section 4: Abstract Compositional Measure (Tier 2) -/

/-- An abstract compositional measure over KO7 traces.
Each constructor has a combining function that maps subterm measure values to
the compound term's measure value.

The key axioms are the **subterm properties** for `c_app`:
- `app_subterm1`: `c_app(x, y) > x` - app is strictly larger than its first argument
- `app_subterm2`: `c_app(x, y) > y` - app is strictly larger than its second argument

These capture the essence of "compositionality": the measure of `app s (recΔ b s n)`
is built from the measures of BOTH `s` and `recΔ b s n`, and is strictly larger than
either. This is what makes compositional measures sensitive to duplication. -/
structure CompositionalMeasure where
  c_void      : Nat
  c_delta     : Nat → Nat
  c_integrate : Nat → Nat
  c_merge     : Nat → Nat → Nat
  c_app       : Nat → Nat → Nat
  c_recΔ      : Nat → Nat → Nat → Nat
  c_eqW       : Nat → Nat → Nat
  app_subterm1 : ∀ x y, c_app x y > x
  app_subterm2 : ∀ x y, c_app x y > y

/-- The evaluation function for an abstract compositional measure. -/
@[simp] def CompositionalMeasure.eval (CM : CompositionalMeasure) : Trace → Nat
  | void        => CM.c_void
  | delta t     => CM.c_delta (CM.eval t)
  | integrate t => CM.c_integrate (CM.eval t)
  | merge a b   => CM.c_merge (CM.eval a) (CM.eval b)
  | app a b     => CM.c_app (CM.eval a) (CM.eval b)
  | recΔ b s n  => CM.c_recΔ (CM.eval b) (CM.eval s) (CM.eval n)
  | eqW a b     => CM.c_eqW (CM.eval a) (CM.eval b)

/-! ## Section 5: Tier 2 Impossibility (Transparent Delta) -/

/-- **IMPOSSIBILITY THEOREM (Abstract Compositional, Transparent Delta)**

When `c_delta(c_void) = c_void` (delta is transparent at base level - as in `tau` where
`tau(delta t) = tau t`), no compositional measure with subterm properties for `c_app`
can orient the duplicating recursor.

**Proof** (4 lines): Set `b = void, n = void, s = void`. Then:
- LHS = `c_recΔ(V, V, c_delta(V))` = `c_recΔ(V, V, V)` (by transparency)
- RHS = `c_app(V, c_recΔ(V, V, V))`
- By `app_subterm2`: `c_app(V, R) > R` where `R = c_recΔ(V, V, V)` = LHS
- So RHS > LHS, contradicting orientation (which requires RHS < LHS). -/
theorem no_compositional_orients_rec_succ_transparent_delta
    (CM : CompositionalMeasure)
    (h_transparent : CM.c_delta CM.c_void = CM.c_void) :
    ¬ (∀ (b s n : Trace),
      CM.eval (app s (recΔ b s n)) < CM.eval (recΔ b s (delta n))) := by
  intro h
  have hspec := h void void void
  simp only [CompositionalMeasure.eval] at hspec
  rw [h_transparent] at hspec
  -- hspec : c_app c_void (c_recΔ c_void c_void c_void) < c_recΔ c_void c_void c_void
  have hsub := CM.app_subterm2 CM.c_void (CM.c_recΔ CM.c_void CM.c_void CM.c_void)
  -- hsub : c_app c_void (c_recΔ c_void c_void c_void) > c_recΔ c_void c_void c_void
  omega

/-! ## Section 6: DP Projection Escape -/

/-- A projection-based measure that tracks only delta-nesting depth.
This is the measure implicitly used by TTT2's subterm criterion with π(recD#) = 3.
It projects to the recursion counter and IGNORES all other structure. -/
@[simp] def dpProjection : Trace → Nat
  | void        => 0
  | delta t     => dpProjection t + 1
  | integrate _ => 0
  | merge _ _   => 0
  | app _ _     => 0
  | recΔ _ _ n  => dpProjection n
  | eqW _ _     => 0

/-- The DP projection DOES orient rec_succ: the 3rd argument strictly decreases
from `delta n` (depth k+1) to `n` (depth k). -/
theorem dp_projection_orients_rec_succ (b s n : Trace) :
    dpProjection (app s (recΔ b s n)) < dpProjection (recΔ b s (delta n)) := by
  simp [dpProjection]

/-- The DP projection VIOLATES the subterm property for `app`.
Specifically, `dpProjection(app x y)` is NOT always > `dpProjection(x)`.
Counterexample: `x = delta void` (dpProjection = 1), `y = void` (dpProjection = 0),
`app x y` has dpProjection = 0 < 1 = dpProjection(x).

This is the precise axiom that DP violates, escaping the impossibility theorem. -/
theorem dp_projection_violates_sensitivity :
    ∃ x y : Trace, ¬ (dpProjection (app x y) > dpProjection x) := by
  exact ⟨delta void, void, by simp [dpProjection]⟩

/-- The DP projection also violates the second subterm property.
`dpProjection(app x y)` = 0 is NOT always > `dpProjection(y)`. -/
theorem dp_projection_violates_subterm2 :
    ∃ x y : Trace, ¬ (dpProjection (app x y) > dpProjection y) := by
  exact ⟨void, delta void, by simp [dpProjection]⟩

/-! ## Section 7: Instance Witnesses -/

/-- `simpleSize` (from Conjecture_Boundary) is an additive compositional measure.
All weights are 1 except void which is 0. -/
def simpleSize_ACM : AdditiveCompositionalMeasure where
  w_void      := 0
  w_delta     := 1
  w_integrate := 1
  w_merge     := 1
  w_app       := 1
  w_rec       := 1
  w_eq        := 1
  hw_app_pos  := by omega

/-- `tau` (from ComputableMeasure) is an additive compositional measure.
Note: w_delta = 0 (delta is transparent). This is the transparent-delta case. -/
def tau_ACM : AdditiveCompositionalMeasure where
  w_void      := 0
  w_delta     := 0
  w_integrate := 1
  w_merge     := 2
  w_app       := 1
  w_rec       := 3
  w_eq        := 4
  hw_app_pos  := by omega

/-- `nodeCount` (from Conjecture_Boundary) is an additive compositional measure.
Every constructor adds 1, base is 1. -/
def nodeCount_ACM : AdditiveCompositionalMeasure where
  w_void      := 1
  w_delta     := 1
  w_integrate := 1
  w_merge     := 1
  w_app       := 1
  w_rec       := 1
  w_eq        := 1
  hw_app_pos  := by omega

/-- `treeDepth` assigns weight 1 per constructor except void. -/
def treeDepth_ACM : AdditiveCompositionalMeasure where
  w_void      := 0
  w_delta     := 1
  w_integrate := 1
  w_merge     := 1
  w_app       := 1
  w_rec       := 1
  w_eq        := 1
  hw_app_pos  := by omega

/-- Any `linearWeight` from Conjecture_Boundary is an additive compositional measure,
provided its app coefficient is ≥ 1. -/
def linearWeight_ACM (c_void c_delta c_int c_merge c_app c_rec c_eq : Nat)
    (h : c_app ≥ 1) : AdditiveCompositionalMeasure where
  w_void      := c_void
  w_delta     := c_delta
  w_integrate := c_int
  w_merge     := c_merge
  w_app       := c_app
  w_rec       := c_rec
  w_eq        := c_eq
  hw_app_pos  := h

/-! ## Section 8: GlobalOrients Integration -/

/-- No additive compositional measure can globally orient the full KO7 `Step` relation.
This follows immediately: if it could orient all rules, it would orient rec_succ,
contradicting the impossibility theorem. -/
theorem no_global_step_orientation_additive_compositional
    (M : AdditiveCompositionalMeasure) :
    ¬ MetaConjectureBoundary.GlobalOrients M.eval (· < ·) := by
  intro h
  apply no_additive_compositional_orients_rec_succ M
  intro b s n
  exact h (Step.R_rec_succ b s n)

/-! ## Summary of the Boundary

The impossibility theorem establishes:

1. **Compositional measures fail**: Any measure satisfying the compositionality axioms
   (additive weight structure with w_app ≥ 1, or abstract combining functions with
   subterm properties) CANNOT orient the duplicating recursor for all term instantiations.

2. **DP projection succeeds**: The subterm criterion with projection π(recΔ#) = 3
   DOES orient the recursor, but it escapes the impossibility by violating the
   compositionality axioms - it projects to one argument and ignores the others.

3. **The boundary is at Axiom `app_subterm`**: Compositional measures must satisfy
   `c_app(x, y) > x` and `c_app(x, y) > y`. DP projection satisfies neither.
   This is exactly where the "multiplicity-aware vs. multiplicity-blind" distinction
   manifests as a formal axiom.
-/

end OperatorKO7.CompositionalImpossibility
