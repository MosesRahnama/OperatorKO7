/-!
# Contract Probes (P1–P3)

These probes document required checks from the Strict Execution Contract.
They are written to be build-safe: negative cases are in comments; no failing assertions.

P1: Branch realism — enumerate clauses, test rfl per-branch, report failures, give corrected laws.
P2: Duplication realism — show additive failure and give the robust DM/MPO orientation premise.
P3: Symbol realism — one success, one unknown identifier example, one arity/type mismatch example.
-/

namespace OperatorKO7.MetaProbes

/- ## P1: Branch realism -/

/-- A tiny two-branch function used to illustrate the P1 "branch realism" check. -/
def f : Nat → Nat
| 0       => 1
| Nat.succ x => x

/-
Clause-by-clause rfl checks for the claim 2 * f x = f (2 * x):

- x = 0:
  LHS = 2 * f 0 = 2 * 1 = 2; RHS = f (2 * 0) = f 0 = 1 → not rfl. Fails.

- x = succ y:
  LHS = 2 * f (succ y) = 2 * y; RHS = f (2 * succ y) = f (2*y + 2) = (2*y + 2).pred = 2*y + 1 → not rfl. Fails.

Corrected per-branch statements:
- x = 0: 2 * f 0 = 2 ≠ 1 = f 0
- x = succ y: 2 * f (succ y) = 2*y and f (2*succ y) = 2*y + 1 differ by 1

True global facts:
- f (2 * x) = Nat.pred (2 * x + 1)
- 2 * f x ≤ 2 * x, with strict inequality when x ≠ 0
- Minimal counterexample to the false global equality: x = 0.
-/

/- ## P2: Duplication realism -/

/-
Consider a rewrite rule that duplicates a subterm S: h(S) → g(S,S).
With a simple node-count measure M, we get:
  M(after) = M(before) - 1 + M(S) + M(S) = M(before) - 1 + 2·M(S),
which is not a strict drop when M(S) ≥ 1.

Robust orientation uses a multiset-of-weights (Dershowitz–Manna) or MPO/RPO:
- Key premise: every RHS piece Pi is strictly < the removed LHS redex W in the base order.
- If we cannot exhibit Pi < W for all pieces, we must declare a CONSTRAINT BLOCKER.
-/
-- (Orientation lemmas live in the main development; this file only documents the probe.)

/- ## P3: Symbol realism -/

/-
One success (present in toolkit):
- Ordinal.opow_le_opow_right : monotonicity of ω^· in the exponent (≤-mono)

One unknown identifier example (NameGate):
- opow_right_mono_strict — SEARCH(name)=0 → must use local bridge `opow_lt_opow_right` instead.

One arity/type mismatch example (TypeGate):
- mul_le_mul_left' used with arguments in wrong order/type; fix by applying the α, β, γ as per lemma’s signature.
-/

end OperatorKO7.MetaProbes
