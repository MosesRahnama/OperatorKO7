# OperatorKO7 - Reviewer Documentation

**Repository:** [MosesRahnama/OperatorKO7](https://github.com/MosesRahnama/OperatorKO7)
**Updated:** February 2026
**Total LOC:** ~6,100 (Lean 4)

This document is a reviewer guide. It maps every file to its role and lists the key theorem names. The source code is the artifact; the paper is the argument. This document is the index.

---

## Build

```bash
git clone https://github.com/MosesRahnama/OperatorKO7.git
cd OperatorKO7
lake update
lake exe cache get    # optional
lake build
```

Lean `v4.22.0-rc4` (pinned in `lean-toolchain`). Dependencies locked in `lake-manifest.json`. CI: GitHub Actions.

---

## Architecture

```
OperatorKO7.lean                 -- library entry point
OperatorKO7/
  Kernel.lean                    -- core calculus (7 constructors, 8 rules)
  Meta/
    SafeStep_Core.lean           -- guarded SafeStep relation + DM toolkit
    ComputableMeasure.lean       -- canonical SN certificate (triple-lex)
    Normalize_Safe.lean          -- certified normalizer
    SafeStep_Ctx.lean            -- context closure + ctx-local-join
    Confluence_Safe.lean         -- local-join library + global discharge
    Newman_Safe.lean             -- Newman's lemma + unconditional confluence
    Conjecture_Boundary.lean     -- 14 no-go theorems (full Step)
    Impossibility_Lemmas.lean    -- additive/flag/constellation barriers
    Operational_Incompleteness.lean -- toy calculus + InternallyDefinableMeasure
    DM_MPO_Orientation.lean      -- DM/MPO helpers
    FailureModes.lean            -- countermodels
    ContractProbes.lean          -- P1-P3 probes
    PaperApproachIndex.lean      -- compile-time paper-code consistency
    CNFOrdinal.lean              -- constructive CNF ordinal
    HydraCore.lean               -- toy hydra core
    GoodsteinCore.lean           -- toy Goodstein core
    ComputableMeasure_Verification.lean
    ComputableMeasure_Test.lean
    Examples_Publish.lean
  Test/
    Sanity.lean                  -- minimal smoke test
```

---

## File-by-file guide

### 1. `Kernel.lean` (59 lines)

Defines the KO7 term language and full kernel relation.

- `Trace`: 7 constructors (`void`, `delta`, `integrate`, `merge`, `app`, `recΔ`, `eqW`)
- `Step`: 8 unconditional root reduction rules
- `StepStar`: reflexive-transitive closure
- `NormalForm`: no outgoing `Step`

### 2. `SafeStep_Core.lean` (156 lines)

Guarded subrelation used by the canonical termination development.

- `weight`, `kappaM`: DM multiset payload
- `deltaFlag`: binary phase detector for `recΔ b s (delta n)`
- `SafeStep`: 8 guarded rules (adds side conditions to `Step`)
- `SafeStepRev`: reverse relation for SN statements

### 3. `ComputableMeasure.lean` (460 lines)

The canonical termination certificate. Key definitions and theorems:

- `tau`: computable Nat-valued head-weighted rank
- `DM`, `LexDM_c`, `Lex3c`: inner and outer lexicographic orders
- `mu3c`: the triple measure `(deltaFlag, kappaM, tau)`
- `drop_R_*_c` (8 lemmas): per-rule strict decrease
- `measure_decreases_safe_c`: master aggregator (all 8 rules)
- **`wf_SafeStepRev_c`**: strong normalization of `SafeStep`

### 4. `Normalize_Safe.lean` (252 lines)

Certified normalizer constructed by well-founded recursion.

- `normalizeSafe`: the normalization function
- `to_norm_safe`: `SafeStepStar t (normalizeSafe t)`
- `norm_nf_safe`: `NormalFormSafe (normalizeSafe t)`
- `normalizeSafe_idempotent`: normalizing twice = normalizing once
- `nf_iff_normalize_fixed`: fixed-point characterization

### 5. `SafeStep_Ctx.lean` (548 lines)

Context closure and ctx-local-join infrastructure.

- `SafeStepCtx`: one-step context closure of `SafeStep`
- `SafeStepCtxStar`: reflexive-transitive closure
- `ctxstar_*` lifting lemmas (integrate, merge, app, rec)
- `LocalJoinSafe_ctx`: local join allowing context-closed stars
- Per-shape local-join lemmas (merge, rec, eqW, integrate)

### 6. `Confluence_Safe.lean` (529 lines)

Local-join lemmas and global discharge. (Not separately listed in the repo glob; imported by `Newman_Safe.lean`.)

- `localJoin_all_safe`: global local-join hypothesis discharge
- Per-root-shape join lemmas
- Context wrappers for eqW cases

### 7. `Newman_Safe.lean` (205 lines)

Newman's lemma and its consequences.

- `LocalJoinAt`, `ConfluentSafe`: definitions
- `newman_safe`: SN + local join => confluence (parameterized)
- `locAll_safe`: global discharge of the local-join hypothesis
- **`confluentSafe`**: unconditional confluence for `SafeStep`
- **`unique_normal_forms_safe`**: unique NFs
- `normalizeSafe_eq_of_star`: star-related terms normalize equally

### 8. `Conjecture_Boundary.lean` (490 lines)

14 machine-checked no-go theorems for the full `Step` relation.

| # | Theorem | What fails |
|---|---------|-----------|
| 1 | `no_fixed_kappa_plus_k` | Additive `kappa + k` |
| 2 | `no_simple_lex_witness` | Simple `(kappa, mu)` lex |
| 3 | `no_global_step_orientation_polyMul` | Polynomial with multiplicative recΔ |
| 4 | `no_global_flag_only_orientation` | Single flag |
| 5 | `no_global_step_orientation_simpleSize` | Additive size |
| 6 | `no_global_step_orientation_nestingDepth` | Nesting depth |
| 7 | `no_global_step_orientation_nodeCount` | Naive multiset (node count) |
| 8 | `no_constellation_strict_drop_rec_succ` | Constellation size |
| 9 | `no_global_step_orientation_simpleSize_strictMono` | Any StrictMono of simpleSize |
| 10 | `no_global_step_orientation_kappa_strictMono` | Any StrictMono of kappa |
| 11 | `dual_barrier_rec_succ_and_merge_void` | Dual barrier (additive + flag) |
| 12 | `no_global_step_orientation_headPrecedence` | Pure head precedence |
| 13 | `no_global_step_orientation_linearWeight` | Linear KBO-style weight (any 7 constants) |
| 14 | `no_global_step_orientation_treeDepth` | Standard tree depth |

### 9. `Impossibility_Lemmas.lean` (386 lines)

Failure witnesses aligned with the paper's impossibility catalog.

- `kappa_plus_k_fails`: additive bump counterexample
- `simple_lex_fails`: 2-component lex counterexample
- `merge_void_raises_flag`: flag non-monotonicity witness
- `constellation_size_not_decreasing`: hybrid measure failure
- `rec_succ_additive_barrier`: the core duplication barrier
- `rec_succ_size_increases`: duplication makes size grow

### 10. `Operational_Incompleteness.lean` (1,188 lines)

Toy arithmetic calculus (7 constructors, 8 rules) for duplication stress testing.

- `InternallyDefinableMeasure`: structure encoding the "operator-definable" contract
- `M_size`: concrete instance using additive size
- DM/MPO orientation witnesses for the duplicating rule r4
- Goodstein/Hydra simulation layer and no-single-step proofs

### 11-16. Supporting modules

| File | Lines | Role |
|------|-------|------|
| `DM_MPO_Orientation.lean` | 51 | DM/MPO helper wrappers |
| `FailureModes.lean` | 94 | Countermodels (branch realism, delta-flag) |
| `ContractProbes.lean` | 67 | P1-P3 contract probe documentation |
| `PaperApproachIndex.lean` | 39 | Compile-time paper-code consistency check |
| `Examples_Publish.lean` | 29 | API smoke tests |
| `ComputableMeasure_Verification.lean` | 241 | Extended verification suite |
| `ComputableMeasure_Test.lean` | 45 | Quick `#check` smoke tests |

### 17-19. Auxiliary cores

| File | Lines | Role |
|------|-------|------|
| `CNFOrdinal.lean` | 1,139 | Constructive CNF ordinal: normalization, comparison, arithmetic |
| `HydraCore.lean` | 35 | Toy hydra relation (duplication flavor) |
| `GoodsteinCore.lean` | 40 | Toy Goodstein base-change relation |

### 20. `Test/Sanity.lean` (11 lines)

Minimal `#eval` and `#check` to verify the toolchain works.

---

## Key theorem quick-reference

| What | Lean name | File |
|------|-----------|------|
| SN for SafeStep | `wf_SafeStepRev_c` | `ComputableMeasure.lean` |
| Per-rule decrease (all 8) | `measure_decreases_safe_c` | `ComputableMeasure.lean` |
| Normalizer existence | `normalizeSafe` | `Normalize_Safe.lean` |
| Normalizer totality | `normalizeSafe_total` | `Normalize_Safe.lean` |
| Normalizer soundness | `normalizeSafe_sound` | `Normalize_Safe.lean` |
| Confluence (unconditional) | `confluentSafe` | `Newman_Safe.lean` |
| Unique normal forms | `unique_normal_forms_safe` | `Newman_Safe.lean` |
| Local-join global discharge | `locAll_safe` | `Newman_Safe.lean` |
| Full-step duplication barrier | `rec_succ_additive_barrier` | `Impossibility_Lemmas.lean` |
| Full-step has rec_succ | `full_step_has_rec_succ_instance` | `Conjecture_Boundary.lean` |

---

## Scope

- All SN, normalizer, and confluence results: **`SafeStep` only**.
- Full-system termination: **not claimed**.
- Full-system confluence: **not claimed** (non-local-join witness at `eqW void void`).
- The 14 no-go barriers in `Conjecture_Boundary.lean`: 12 are machine-checked theorems; 2 (local helper lemmas, path orders) are meta-theoretical/methodological.
