import OperatorKO7.Meta.OrdinalHierarchy

/-!
# Invalid relaxed-control route for strict S142

This file records a failed route that looked plausible but is not sound:
allowing one-step descent to *any* smaller notation beneath the chosen
fundamental-sequence approximation and trying to bound the resulting path
length by `cichon o k` via same-control ordinal monotonicity.

That monotonicity principle is false. A concrete counterexample is:

- `cichon 5 1 = 5`
- `cichon ω 1 = 3`

even though `5 < ω`.

So a generic theorem of the form

```lean
a.repr ≤ b.repr → cichon a k ≤ cichon b k
```

cannot be used to justify the relaxed-below-approximant relation. The
correct strict-S142 route must instead use either:

- a norm-bounded control theorem, or
- a more specialized KO7 root comparison that avoids this false monotonicity.

This file is intentionally limited to the counterexample and the exploratory
relation definition; it does **not** provide a valid derivation-length bound.
-/

open ONote

namespace OperatorKO7.OrdinalHierarchy

def omegaNote : ONote := ONote.oadd 1 1 0

example : cichon (ONote.ofNat 5) 1 = 5 := by native_decide

example : cichon omegaNote 1 = 3 := by native_decide

theorem not_cichon_mono_repr :
    ¬ ∀ a b : ONote, ∀ k : Nat, a.repr ≤ b.repr → cichon a k ≤ cichon b k := by
  intro hmono
  have hle : (ONote.ofNat 5).repr ≤ omegaNote.repr := by
    simpa [omegaNote] using (Ordinal.nat_lt_omega0 5).le
  have hbad := hmono (ONote.ofNat 5) omegaNote 1 hle
  have hcontra : ¬ cichon (ONote.ofNat 5) 1 ≤ cichon omegaNote 1 := by
    native_decide
  exact hcontra hbad

/-! ## Relaxed controlled descent relation -/

/-- Relaxed controlled descent: at each step, the path may jump to any
    notation whose `repr` is at most the fundamental-sequence approximation
    (predecessor for successors, `f(k)` for limits).

    This subsumes exact descent (landing exactly at the approximation)
    and below-descent (landing strictly below it). The KO7 `rec_succ`
    rule requires the below-descent case because its ordinal drop can
    skip past the canonical approximant. -/
inductive ControlledPow : ONote → Nat → Nat → Prop
  | refl (o : ONote) (k : Nat) : ControlledPow o k 0
  | succ {o a t : ONote} {k n : Nat}
      (hfs : fundamentalSequence o = Sum.inl (some a))
      (hle : t.repr ≤ a.repr)
      (hrest : ControlledPow t (k + 1) n) :
      ControlledPow o k (n + 1)
  | limit {o t : ONote} {f : Nat → ONote} {k n : Nat}
      (hfs : fundamentalSequence o = Sum.inr f)
      (hle : t.repr ≤ (f k).repr)
      (hrest : ControlledPow t (k + 1) n) :
      ControlledPow o k (n + 1)

/-- Length-only existential projection. -/
abbrev ControlledPath (o : ONote) (k n : Nat) : Prop :=
  ControlledPow o k n

end OperatorKO7.OrdinalHierarchy
