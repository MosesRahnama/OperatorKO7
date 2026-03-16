# Impossibility dead-end notes

This file holds historical dead-end commentary that used to live in
`OperatorKO7/Meta/Impossibility_Lemmas.lean`.

The main theorem file now keeps only compiling witnesses and cited lemmas.
These notes remain here for reproducibility and future extension work.

## Right-add hazard

One abandoned proof shape tried to transport strict inequalities through
ordinal right-addition:

- bad shape: `p < q -> p + s < q + s`

This is not valid for ordinals in general, because right-addition is not
strictly monotone in the left argument across arbitrary right summands.

## "Quick ≤ patch"

Another abandoned fix tried to weaken an equality side condition to `≤`.
That does not repair the nested-`delta` counterexample. The underlying problem
is structural, not a missing monotonicity inequality.

## Status

These are documentation notes only. They are not intended to compile as Lean
declarations, and they are deliberately kept outside theorem-bearing files.
