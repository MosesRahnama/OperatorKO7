# OperatorKO7: One-Month Additions Report

**Window.** Approximately 2026-03-19 through 2026-04-18 (last 30 days).

**Scope.** Every `.lean` module, script, and `Docs/` file touched or added in
the window, organized by the layer of the theorem stack it occupies. For each
file the report states what it does and how it fits into the stack above and
below it.

**Build status.** `lake build OperatorKO7` is green. Paper A
(`Rahnama_The_Orientation_Boundary.tex`) compiles to 57 pages with no LaTeX
errors and no undefined references.

**Counts.** 92 `.lean` files touched in the window; 21 of those are brand-new
files (first landed inside the window), the remaining 71 were modified.
Additional artefacts: 4 Python scripts (1 new), 6 `Docs/` files (4 new),
3 repo-root reports (all new).

---

## Layer 0 — Kernel and primitive step-duplicating schema

The schema foundation that every downstream module consumes.

### [Meta/StepDuplicatingSchema.lean](OperatorKO7/Meta/StepDuplicatingSchema.lean) (595 lines)

Home of `StepDuplicatingSchema`, `StepDuplicatingSystem`, `GlobalOrients`, and
the three canonical measure structures (`AdditiveMeasure`, `AffineMeasure`,
`CompositionalMeasure`). Over the window this file grew across four passes:

1. **Projection-rank extensionality**: `ProjectionRank.ext`,
   `ProjectionRank.ext_rank`.
2. **Confession-core intermediate layer**: `ConfessionCoreWitness` structure
   sitting between `ProjectionRank` and the per-route witness objects, with
   mutually inverse bridges `toProjectionRank` / `ofProjectionRank` and
   four roundtrip simp lemmas; plus `ConfessionCoreWitness.ext` and
   `ConfessionCoreWitness.ext_rank`.
3. **Semantic-profile layer**: four behavioural predicates
   `NormalizedAtBase`, `TracksSuccessorDepth`, `ForgetsWrapperPayload`,
   `FollowsRecursiveCounter`; builders `ConfessionCoreWitness.ofSemanticProfile`
   and the equivalence `satisfies_semantic_profile`; derivation theorems
   `semanticProfile_orients_dup_step`,
   `semanticProfile_violates_wrap_subterm1`,
   `semanticProfile_violates_wrap_subterm2`.
4. **Initiality / uniqueness layer**: `GeneratedByConstructors` (schema-level
   induction principle); `semanticProfile_unique_of_generated` (behaviour
   determines rank on generated schemas); `ConfessionCoreWitness.unique_of_generated`;
   `projectionRank_unique_of_generated`.

**Where it fits.** This is the only module in Layer 0. Everything above it
(barriers, diagnostics, confession family, operational incompleteness) is
parameterized over `StepDuplicatingSchema S` or `StepDuplicatingSystem Sys`.

### [Meta/FreeStepDuplicatingSyntax.lean](OperatorKO7/Meta/FreeStepDuplicatingSyntax.lean) **[NEW, 86 lines]**

The canonical generated instance of the schema. Defines `FreeTerm` inductively,
builds `freeSchema : StepDuplicatingSchema` and the initiality record
`freeSchemaGenerated : GeneratedByConstructors freeSchema` via structural
induction. Supplies `freeCounterDepth`, `freeProjectionRank`,
`freeConfessionCoreWitness`, and two uniqueness consequences
`freeProjectionRank_unique`, `freeConfessionCoreWitness_unique`.

**Where it fits.** Gives the schema-level uniqueness theorems from Layer 0 a
concrete worked carrier. Consumers who need "the confession core is unique"
can instantiate at `freeSchema` and get it for free by structural induction.

### [Meta/FreeStepDuplicatingTraceBridge.lean](OperatorKO7/Meta/FreeStepDuplicatingTraceBridge.lean) **[NEW, 126 lines]**

Bridges the free syntax from the module above to the KO7 `Trace` carrier.
Provides `embedFreeTerm : FreeTerm → Trace`, partial erasure
`eraseTraceToFreeTerm : Trace → Option FreeTerm`, the erase/embed roundtrip
`erase_embedFreeTerm`, injectivity `embedFreeTerm_injective`, and four
per-route theorems stating that each confession route restricts to
`freeCounterDepth` on the embedded fragment
(`dpProjection_on_embedFreeTerm`, `counterProjectionRankFn_on_embedFreeTerm`,
`sctRankFn_on_embedFreeTerm`, `argumentFilteringRankFn_on_embedFreeTerm`),
packaged as `all_confession_routes_factor_through_embedFreeTerm`.

**Where it fits.** Layer 0 talks to KO7. Certifies that KO7's confession ranks
are literally the free-syntax counter depth composed with an embedding, not
merely an equality that happens to hold. This is the formal content behind
Paper A Remark 4.3 ("the schema applies to a second named TRS") and the
companion precision statement "the barrier is visible on the primitive
fragment before the KO7-specific constructors are added".

---

## Layer 1 — Direct barrier theorems (the twelve-family stack)

### [Meta/QuadraticBarrier.lean](OperatorKO7/Meta/QuadraticBarrier.lean)

The restricted quadratic counter barrier (Paper A Thm 4.3) over the schema,
plus KO7 specializations. Modified within the window to keep its signatures
aligned with the new `ProjectionRank` / `ConfessionCoreWitness` layer.

### [Meta/WPO_PolynomialBarrier.lean](OperatorKO7/Meta/WPO_PolynomialBarrier.lean)

WPO-facing direct polynomial-branch corollary of the bounded-polynomial
barrier.

### [Meta/MatrixBarrierLexD.lean](OperatorKO7/Meta/MatrixBarrierLexD.lean) (16 declarations)

Arbitrary-dimension tracked-primary lexicographic barrier (Paper A Thm 4.12).
`MatrixLexMeasureD` + `primaryAffine` + `HasUnboundedPrimaryRange` plus the
four theorem families (unbounded, succ-pump, wrap-pump, pumped-subclass),
with KO7 specializations.

### [Meta/MatrixBarrierLexPermD.lean](OperatorKO7/Meta/MatrixBarrierLexPermD.lean) (12 declarations)

Permutation-priority tracked-primary lex barrier. Same pattern as
`MatrixBarrierLexD` but with an arbitrary priority permutation that keeps
the tracked primary coordinate first.

### [Meta/ProjectedPrimaryBarrier.lean](OperatorKO7/Meta/ProjectedPrimaryBarrier.lean) (7 theorems)

Paper A Thm 4.15 projected-primary dominance meta-theorem. The key theorem
`no_orients_dup_step_of_projected_primary_dominance` subsumes the tracked
componentwise and tracked-primary lex cases; two rederivation theorems
confirm that reduction on the earlier modules.

### [Meta/DepthBarrier.lean](OperatorKO7/Meta/DepthBarrier.lean)

Max-aggregative depth barrier. Earlier in the window this was lifted from
KO7-only to schema-level (`StepDuplicatingSchema.MaxDepthMeasure` with
`no_maxDepth_orients_dup_step` and `no_global_orients_maxDepth`). The KO7
corollary `no_global_step_orientation_maxDepth` now derives via
`toSchemaMeasure`; `standardTreeDepthMeasure` and
`no_global_step_orientation_standardTreeDepth` preserved.

**Where this block fits.** These are all direct barrier theorems sitting
above Layer 0 and below Layer 3's diagnostic analysis. The `SchemaAPI`
public surface re-exports them.

---

## Layer 2 — Schema-level quantitative / diagnostic layer (Paper 2 §3)

Eight new files mechanize Paper 2's quantitative trace analysis at schema
level. All parametric over `BaseDuplicatingSystem` (the schema plus an
explicit base rule) or structure-free where possible.

### [Meta/SchemaCanonicalTrace.lean](OperatorKO7/Meta/SchemaCanonicalTrace.lean) **[NEW]**

`BaseDuplicatingSystem` extension of `StepDuplicatingSystem`, iterated
counter / wrapper chain / canonical trace state, reflexive-transitive
closure `StepStar`, wrap-context closure as an explicit hypothesis, the
two canonical-stage steps (`canonical_dup_step`, `canonical_base_step`),
the multi-step canonical trace law under closure
(`canonical_stage_step`, `canonical_trace_to_base_stage`), and the three
trace coordinates `trace_ctr` / `trace_pay` / `trace_wraps` with
Paper 2 Prop 3.6 (`per_step_exchange`) and Prop 3.8
(`offset_conservation`).

### [Meta/SchemaOffsetAndWrapper.lean](OperatorKO7/Meta/SchemaOffsetAndWrapper.lean) **[NEW]**

Paper 2 Defs 3.9–3.10 (wrapper-cell weight and wrapper stack), Prop 3.12
(permutation gauge symmetry), Prop 3.13 (counter is the gauge-invariant
retained coordinate). Introduces `PayloadTuple`, `constTuple`, `Perm`,
`payloadMass` (additive observer via `Finset.sum`), and proves
`payloadMass_permute` via `Fintype.sum_equiv` — an honest Mathlib-backed
permutation invariance rather than a trivial consequence of the constant
tuple being fixed. Also `payloadMass_constTuple_strict_mono` (multiplicity
sensitivity), `trace_ctr_reversible`,
`counter_unique_retained_coordinate`, `permutation_gauge_symmetry_package`.

### [Meta/SchemaConfessionDominance.lean](OperatorKO7/Meta/SchemaConfessionDominance.lean) **[NEW]**

Paper 2 Props 3.4, 3.7, 3.11. `residualProofWork`, `confessedBurdenDoubled`,
`totalConfessedBurdenDoubled` (doubled to avoid Nat division), closed-form
summation `sum_payloads_doubled`, product-form dominance
`confession_dominance_product`, and the cross-multiplied monotonicity
`proof_entropy_nondecreasing`. The non-negative difference of the
cross-multiplied inequality is `p(k + c*)` in the nontrivial regime and
`p c*` in the trailing regime.

### [Meta/SchemaNormMismatch.lean](OperatorKO7/Meta/SchemaNormMismatch.lean) **[NEW, 261 lines]**

Paper 2 Prop 3.15 (norm mismatch on the diagonal),
Defs 3.16 and 3.18 (gauge entropy, inefficiency coefficient),
Prop 3.19 (η → ∞), Prop 3.20 (Shannon-uniqueness).

Nat-level core: `ell0NormOnDiagonal` / `ellInfNormOnDiagonal` /
`ell1NormOnDiagonal`, `norm_mismatch_pairwise`, `diagonal_norm_values`,
`shannon_uniqueness_gap`, `inefficiency_doubled_burden_lower_bound`.

Real-analysis upgrade (via `Mathlib.Analysis.SpecialFunctions.Log.Basic`):
`gaugeEntropy`, `inefficiencyCoefficient`, `inefficiencyCoefficient_lower_linear`,
`inefficiencyCoefficient_unbounded`, `inefficiencyCoefficient_unbounded_atTop`
(the `∀ N, ∃ k, N ≤ η(k, w)` statement).

Explicit description-length block: `repeatedCarrierMass`,
`explicitDescriptionLength`, `explicitDescriptionLength_upper_bound`,
`repeatedCarrierMass_description_balance`, `explicitDescription_linear_gap`
(Paper 2 Prop 3.20 as an **equality** rather than an inequality, up to
the logarithmic index code `Nat.size (i + 1)` and fixed glue overhead).

### [Meta/SchemaSeedCarrierFactorization.lean](OperatorKO7/Meta/SchemaSeedCarrierFactorization.lean) **[NEW]**

Paper 2 Def 3.21 (collapse map), Prop 3.22 (factorization criterion),
Cor 3.23 (additive vs seed observable). Deliberately structure-free;
does not reference `StepDuplicatingSchema` at all. Provides
`Diagonal`, `collapse`, `PayloadObservable`, `CarrierInsensitive`,
`FactorsThroughCollapse`, `factorization_criterion` (biconditional),
`factorization_unique`, `additiveObservable`, `seedObservable`,
`seedObservable_factors`, `additiveObservable_not_factors`.

**Where Layer 2 fits.** These eight modules (plus the
free-syntax / trace-bridge from Layer 0) supply Paper 2 §3's quantitative
content at the schema level. Paper A §3.1.5 and Paper A §5 "Schema-level
diagnostic layer" cite them by identifier.

---

## Layer 3 — Forgetting witness and schema operational incompleteness (Paper 2 §4–5)

### [Meta/SchemaForgettingWitness.lean](OperatorKO7/Meta/SchemaForgettingWitness.lean) **[NEW, 118 lines]**

The schema-generic `ForgettingWitness S` record: orientation of the
duplicating step plus wrapper-sensitivity violations on both payload
positions. Four builders:

- `ForgettingWitness.ofProjectionRank` (from any projection rank)
- `ForgettingWitness.ofConfessionCoreWitness` (via the intermediate layer)
- `ForgettingWitness.ofSemanticProfile` (directly from the four
  behavioural predicates, bypassing `ProjectionRank`)
- `ConfessionMethod.toForgettingWitness` (from any confession method)

### [Meta/SchemaWitnessOrder.lean](OperatorKO7/Meta/SchemaWitnessOrder.lean) **[NEW]**

Paper 2 §4 witness-order layer. Local `WLevel` (four coarse levels),
`SchemaWitnessTower S`, `kappaLe`, `kappaGt`, `OB` (orientation-boundary
predicate), `OB_iff_no_directWhole` (biconditional),
`OB_witness_at_transformedCall`, `boundary_threshold_at_transformedCall`.

### [Meta/SchemaOperationalIncompleteness.lean](OperatorKO7/Meta/SchemaOperationalIncompleteness.lean) **[NEW]**

Paper 2 §5 operational-incompleteness layer in two forms.

**Abstract form:** `OperationalQuestion Statement` (generic proof-language
interface), `OperationallyIncomplete` (Paper 2 Def 5.1),
`DirectAggregationClaim`, `directAggregationQuestion`, and
`directAggregationQuestion_operationallyIncomplete` (Paper 2 Thm 5.2 in
abstract form).

**Concrete form:** `OperationalIncompleteness Sys` evidence bundle with
the three direct-barrier negations plus a forgetting witness;
`OperationalIncompleteness.ofProjectionRank` (Paper 2 Thm 5.2 canonical
instance), `operationalIncompleteness_universal` (Paper 2 Cor 5.3);
`canonical_operational_instance` (both forms from one projection rank).

**Construction vs confession:** `ConstructionResponse`, `ConfessionResponse`
(Paper 2 Defs 5.8–5.9), `construction_confession_exclusive` (Paper 2
Prop 5.10).

**Projection-transaction:** `ProjectionTransaction`,
`IsStaticProjectionFamily`, `projection_transaction_static`
(Paper 2 Def 5.16, Prop 5.17).

**Where Layer 3 fits.** Takes Layer 0's schema primitives plus Layer 2's
quantitative identities and assembles them into the paper-facing
abstractions used in Paper 2 §4 and §5. Paper A §5 "Schema-level
diagnostic layer" cites these directly.

---

## Layer 4 — Confession-method family and the unification layer

The four W2 confession routes (DP, direct counter-projection, SCT,
argument filtering) plus their convergence layer.

### [Meta/ConfessionMethod.lean](OperatorKO7/Meta/ConfessionMethod.lean) (67 lines)

Generic interface. `SoundnessLicense` enum, `ConfessionMethod S extends
ProjectionRank S`, `ConfessionMethod.toConfessionCoreWitness` bridge,
`confession_orients`, `confession_violates_wrap1`,
`confession_violates_wrap2`. Dropped the unused `OperationalIncompleteness`
import in the window.

### [Meta/ConfessionMethod_DP.lean](OperatorKO7/Meta/ConfessionMethod_DP.lean) (80 lines)

Dependency-pair route. `DPWitness` structure with `selectedCoordinate`,
`schemaDPWitness`, `DPWitness.toConfessionCoreWitness`, `dpConfession`
(license: Arts–Giesl 2000), `dpConfession_is_canonical`,
`dpWitness_has_semantic_profile`.

### [Meta/ConfessionMethod_CounterProjection.lean](OperatorKO7/Meta/ConfessionMethod_CounterProjection.lean) (147 lines)

Direct counter-projection. `DirectCounterProjectionWitness`,
`counterProjectionRankFn` (independent recursive rank on `Trace`), the
convergence theorem `counterProjectionRankFn_eq_dpProjection` (proved by
induction), `counterProjectionDerivedRank`, `counterProjectionConfession`
(license: subterm-criterion-direct), `counterProjection_eq_dp_rank`,
`directCounterProjectionWitness_has_semantic_profile`.

### [Meta/ConfessionMethod_SCT.lean](OperatorKO7/Meta/ConfessionMethod_SCT.lean) (223 lines)

Size-change termination. `SCArc`, `SizeChangeGraph`, `schemaRecCallGraph`,
per-coordinate descent theorems, `sctSatisfied`,
`schema_sct_satisfied`, `schema_sct_unique_descent`, `SCTWitness`
structure, `sctWitness_selects_counter_coordinate`, `sctRankFn`,
`sctRankFn_eq_dpProjection`, `sctDerivedRank`, `sctConfession` (license:
Lee–Jones–Ben-Amram 2001), `sct_eq_dp_rank`,
`sctWitness_has_semantic_profile`.

### [Meta/ConfessionMethod_ArgumentFiltering.lean](OperatorKO7/Meta/ConfessionMethod_ArgumentFiltering.lean) (150 lines)

Argument filtering. `ArgumentFilteringWitness`, `argumentFilteringRankFn`,
`argumentFilteringRankFn_eq_dpProjection`, `argumentFilteringDerivedRank`,
`argumentFilteringConfession` (license: argument-filtering soundness),
`argumentFiltering_eq_dp_rank`,
`argumentFilteringWitness_has_semantic_profile`.

### [Meta/ConfessionMethod_Family.lean](OperatorKO7/Meta/ConfessionMethod_Family.lean) (186 lines)

Family aggregator. `allConfessionMethods` list, `family_size`,
`family_rank_agreement` (now derived from the per-route convergence
theorems, not an alias equality), `family_orients_dup_step`,
`family_violates_sensitivity`, `family_certified_forgetting`,
`family_distinct_licenses`, `family_single_core`,
`family_independent_entries_and_single_core`, `confession_is_a_class`
(main structural-class theorem),
`confession_family_resolves_operational_incompleteness`,
`family_terminates_pair_problem`, `ko7_full_system_terminates`,
`ko7_full_context_closed_terminates`.

### [Meta/ConfessionMethod_Unification.lean](OperatorKO7/Meta/ConfessionMethod_Unification.lean) **[NEW, 506 lines]**

The convergence layer. Names `confessionProjectionCore` (the shared core),
`confessionCoreWitness`, per-route core witnesses (`dpCoreWitness`,
`counterProjectionCoreWitness`, `sctCoreWitness`,
`argumentFilteringCoreWitness`), plus extensive convergence theorems at
five levels of abstraction:

- Level 1 (rank equality) — handled by Layer 4's per-route files.
- Level 2 (projection-rank equality) — `dp_route_eq_confession_core` etc,
  `all_confession_routes_share_projection_core`.
- Level 3 (core-witness equality) —
  `all_route_local_witnesses_share_confession_core_witness_exact`,
  `all_confession_methods_share_confession_core_witness_exact`.
- Level 4 (semantic profile) — `confession_core_has_semantic_profile`,
  `all_confession_methods_share_semantic_profile`,
  `all_route_local_witnesses_have_semantic_profile_directly`.
- Level 5 (KO7-local extended-profile uniqueness) — `CollapsesIntegrate`,
  `CollapsesMerge`, `CollapsesEqW` (KO7 side-condition predicates for the
  non-schema constructors), `confession_core_has_ko7_extended_semantic_profile`,
  `ko7_extended_semantic_profile_unique` (any rank satisfying the seven
  extended-profile predicates on KO7 equals `dpProjection`, proved by
  induction on `Trace`),
  `all_route_local_witnesses_have_ko7_extended_semantic_profile`,
  `all_route_local_witnesses_converge_by_extended_semantic_profile`.

Also defines semantic-profile forgetting witnesses per route
(`dpSemanticForgettingWitness`, `counterProjectionSemanticForgettingWitness`,
`sctSemanticForgettingWitness`, `argumentFilteringSemanticForgettingWitness`)
obtained directly from `ForgettingWitness.ofSemanticProfile` applied to the
`_has_semantic_profile` evidence, plus the roundtrip sanity check
`all_route_local_witnesses_yield_semantic_forgetting_witnesses`. Closes
with the strong convergence summary `confession_routes_converge`.

**Where Layer 4 fits.** Above Layer 0 (uses `ProjectionRank`,
`ConfessionCoreWitness`) and Layer 3 (uses `ForgettingWitness`). Produces
the W2 family that Paper A §4.10 and Paper 2 §5 refer to as "the
confession-method family".

---

## Layer 5 — SCC barrier extensions

All schema-level; none depend on KO7 syntax. Delayed-duplication family on
the left, multiplicity-preserving family on the right, graph / SCC
extraction utilities in the middle.

### Delayed-duplication SCC family

- [Meta/MutualDuplication_General.lean](OperatorKO7/Meta/MutualDuplication_General.lean) — bounded two-node alternating SCC; `AlternatingDupSchema`, additive and affine composite-step barriers.
- [Meta/MutualDuplication_CycleFlow.lean](OperatorKO7/Meta/MutualDuplication_CycleFlow.lean) — abstract one-cycle metatheorems: additive, affine, compositional-transparent, scalar-projection.
- [Meta/MutualDuplication_KNode.lean](OperatorKO7/Meta/MutualDuplication_KNode.lean) — finite cyclic `k+1`-node generalization.
- [Meta/MutualDuplication_KNode_Abstract.lean](OperatorKO7/Meta/MutualDuplication_KNode_Abstract.lean) — bridge from finite `k+1`-node to abstract cycle layer.
- [Meta/MutualDuplication_GraphCycle.lean](OperatorKO7/Meta/MutualDuplication_GraphCycle.lean) — raw-graph delayed-duplication with `CyclePath` and the same four barrier corollaries.
- [Meta/MutualDuplication_Transparent.lean](OperatorKO7/Meta/MutualDuplication_Transparent.lean) — transparent-compositional + projected matrix-style extension of the alternating SCC.

### Multiplicity-preserving SCC family

- [Meta/MutualDuplication_PayloadFlow.lean](OperatorKO7/Meta/MutualDuplication_PayloadFlow.lean) — abstract `PacketModel T` metatheorems.
- [Meta/MutualDuplication_Preserving.lean](OperatorKO7/Meta/MutualDuplication_Preserving.lean) — concrete synchronized-packet two-node instance; additive and conditional affine barriers.
- [Meta/MutualDuplication_Preserving_KNode.lean](OperatorKO7/Meta/MutualDuplication_Preserving_KNode.lean) — finite cyclic packet generalization.
- [Meta/MutualDuplication_Preserving_Abstract.lean](OperatorKO7/Meta/MutualDuplication_Preserving_Abstract.lean) — bridge to the abstract payload-flow layer.
- [Meta/MutualDuplication_Preserving_Transparent.lean](OperatorKO7/Meta/MutualDuplication_Preserving_Transparent.lean) — packet-transparent + projection corollaries.
- [Meta/MutualDuplication_PacketGraph.lean](OperatorKO7/Meta/MutualDuplication_PacketGraph.lean) — raw-graph synchronized-packet version.

### Graph / SCC extraction utilities

- [Meta/GraphPathExtraction.lean](OperatorKO7/Meta/GraphPathExtraction.lean) — `EdgePath`, `ofTransGen`, `ofRoundTrip`, `ofClosedTransGen`.
- [Meta/FiniteGraphReachability.lean](OperatorKO7/Meta/FiniteGraphReachability.lean) — `Reachable`, `reachable_iff_reflTransGen`, `transGen_of_reachable_of_ne`.
- [Meta/FiniteGraphSCC.lean](OperatorKO7/Meta/FiniteGraphSCC.lean) — `sccPairs`, `HasNontrivialSCC`, `witnessPair`.
- [Meta/MutualDuplication_RelationalGraph.lean](OperatorKO7/Meta/MutualDuplication_RelationalGraph.lean) — relation-level construction of the delayed or preserving raw-graph SCC automatically.
- [Meta/MutualDuplication_CallGraph.lean](OperatorKO7/Meta/MutualDuplication_CallGraph.lean) — call-graph construction from extracted `nodeKey` / `succKeys` data.
- [Meta/MutualDuplication_ExtractedCallGraph.lean](OperatorKO7/Meta/MutualDuplication_ExtractedCallGraph.lean) — array-backed construction from raw extracted node data indexed by `Fin nodes.size`.

**Where Layer 5 fits.** Sits above Layer 0 and parallel to Layer 1. Extends
the direct barrier stack (Paper A Thms 4.22–4.23) from single-rule duplication
to SCC-shaped patterns, with the raw-graph formulations allowing arbitrary
node / edge systems.

---

## Layer 6 — Dependency-pair extraction stack

Generic first-order DP extraction tooling. Modified across the window to
match the new confession-method surface.

- [Meta/DependencyPairs_Fragment.lean](OperatorKO7/Meta/DependencyPairs_Fragment.lean) — schema-level rank / SCC-path descent fragment.
- [Meta/DependencyPairs_FiniteGraph.lean](OperatorKO7/Meta/DependencyPairs_FiniteGraph.lean) — finite DP graph interface reusing the finite-SCC search layer.
- [Meta/DependencyPairs_CallGraph.lean](OperatorKO7/Meta/DependencyPairs_CallGraph.lean) — finite DP call-graph from `nodeKey` / `succKeys` data.
- [Meta/DependencyPairs_ExtractedCallGraph.lean](OperatorKO7/Meta/DependencyPairs_ExtractedCallGraph.lean) — array-backed extracted call-graph.
- [Meta/DependencyPairs_TPDBExtraction.lean](OperatorKO7/Meta/DependencyPairs_TPDBExtraction.lean) — TPDB-side DP extraction from a finite rule list.
- [Meta/DependencyPairs_FirstOrderExtraction.lean](OperatorKO7/Meta/DependencyPairs_FirstOrderExtraction.lean) — generic first-order DP extraction over arbitrary symbols and variables.
- [Meta/DependencyPairs_FirstOrderFrontend.lean](OperatorKO7/Meta/DependencyPairs_FirstOrderFrontend.lean) — rule-record frontend for the generic extractor.
- [Meta/DependencyPairs_FirstOrderEngine.lean](OperatorKO7/Meta/DependencyPairs_FirstOrderEngine.lean) — consolidated engine-level frontend with typeclass-based views.
- [Meta/DependencyPairs_HeadView.lean](OperatorKO7/Meta/DependencyPairs_HeadView.lean) — minimal head / call-head bridge for engines that only expose head data.
- [Meta/DependencyPairs_FiniteCarrierView.lean](OperatorKO7/Meta/DependencyPairs_FiniteCarrierView.lean) — finite-carrier bridge for engines whose rules form a finite type.
- [Meta/DependencyPairs_KernelFirstOrder.lean](OperatorKO7/Meta/DependencyPairs_KernelFirstOrder.lean) — KO7-symbol frontend packaging all eight KO7 rules through the consolidated stack.

**Where Layer 6 fits.** Above Layer 0 (uses `StepDuplicatingSchema` and
`Meta/DependencyPairs_Fragment`). Produces the dependency-pair artefacts
consumed by Paper A §4.10 and by the `TPDB_Export` / `TTT2_CertificateReplay`
artefact-bridge files.

---

## Layer 7 — Complexity, confluence, and ordinal calibration

Spine of the KO7 certification chain. All modified within the window,
several substantially.

### Complexity

- [Meta/ContextualCopyBudget.lean](OperatorKO7/Meta/ContextualCopyBudget.lean) — `ctxDupPotential` position-aware multiplicity potential plus the strict descent proof; Paper A Prop 5.7 core.
- [Meta/ContextualCopyBudget_NoGo.lean](OperatorKO7/Meta/ContextualCopyBudget_NoGo.lean) — auxiliary contextual coordinates and the no-go theorem for the older monotone-arithmetic candidate.
- [Meta/SafeStepCtx_Complexity_Exponential.lean](OperatorKO7/Meta/SafeStepCtx_Complexity_Exponential.lean) — public single-exponential `SafeStepCtx` envelope.
- [Meta/SafeStepCtx_Complexity_LowerBound.lean](OperatorKO7/Meta/SafeStepCtx_Complexity_LowerBound.lean) — Paper A Prop 5.9 explicit exponential lower family; `safeStepCtxPow_trans`, context-propagation lemmas, `ctxLowerFamily*`, `two_pow_le_ctxLowerLen`, three `has_singleExponential_*_family` theorems.
- [Meta/SafeStepCtx_Complexity_Cichon.lean](OperatorKO7/Meta/SafeStepCtx_Complexity_Cichon.lean) — `cichon`-wrapper around the exponential theorem.
- [Meta/SafeStep_Complexity_Ordinal.lean](OperatorKO7/Meta/SafeStep_Complexity_Ordinal.lean) — legacy `ctxFuel`-based tower-bound, retained as a coarse corollary.
- [Meta/SafeStep_Complexity_MW_Root.lean](OperatorKO7/Meta/SafeStep_Complexity_MW_Root.lean) — `cichon` notation bridge for the calibrated root measure.
- [Meta/SafeStep_Complexity_MW_Ctx.lean](OperatorKO7/Meta/SafeStep_Complexity_MW_Ctx.lean) — conservative contextual `cichon` lift with the obstruction `not_all_safeStepCtx_rootNote_drop`.
- [Meta/SafeStep_Complexity_MW_CtxExact.lean](OperatorKO7/Meta/SafeStep_Complexity_MW_CtxExact.lean) — Paper A Prop 5.11 direct exact contextual extraction on a separate finite note package; `ctxExactNote`, `ctxExactBound`, `safeStepCtx_exact_step`, `safeStepCtxPow_exact_drop`, `safestepctx_length_le_ctxExactBound`.
- [Meta/SafeRoot_Complexity.lean](OperatorKO7/Meta/SafeRoot_Complexity.lean) — exact path and envelopes for the certified root normalizer.
- [Meta/Reachability_Complexity.lean](OperatorKO7/Meta/Reachability_Complexity.lean) — explicit decision-cost envelope for reachability.

### Confluence

- [Meta/SafeStepCtx_Confluence.lean](OperatorKO7/Meta/SafeStepCtx_Confluence.lean) — **Paper A Prop 5.3** discharged contextual local-join; `localJoinAll_ctx`, `confluentSafeCtx`, `confluentSafeCtx_iff_localJoinAll`.
- [Meta/Newman_Safe.lean](OperatorKO7/Meta/Newman_Safe.lean) — `confluentSafe`, `reachability_decidable`.

### Ordinal calibration

- [Meta/DM_OrderType.lean](OperatorKO7/Meta/DM_OrderType.lean) — Dershowitz–Manna to ordinal embedding.
- [Meta/DM_UpstreamSurface.lean](OperatorKO7/Meta/DM_UpstreamSurface.lean) — upstream-prep staging surface.
- [Meta/Mu3c_Image_LowerBound.lean](OperatorKO7/Meta/Mu3c_Image_LowerBound.lean) — realized lower-bound families for the full triple-lex image.

**Where Layer 7 fits.** Between Layer 0 / KO7 kernel and Paper A §5
certification chain. Paper A cites these through the "Certification and
ordinal-calibration" claim-to-code table.

---

## Layer 8 — Certified-measure infrastructure and kernel-level artefacts

- [Meta/ComputableMeasure.lean](OperatorKO7/Meta/ComputableMeasure.lean) — triple-lex guarded `SafeStep` measure.
- [Meta/ComputableMeasure_Verification.lean](OperatorKO7/Meta/ComputableMeasure_Verification.lean) — sanity checks.
- [Meta/BarrierWitness.lean](OperatorKO7/Meta/BarrierWitness.lean) — three canonical barrier-witness extractors (`additive_witness`, `compositional_witness`, `affine_witness`).
- [Meta/BarrierWitness_Budgets.lean](OperatorKO7/Meta/BarrierWitness_Budgets.lean) — canonical witness-budget packaging.
- [Meta/CompositionalMeasure_Impossibility.lean](OperatorKO7/Meta/CompositionalMeasure_Impossibility.lean) — KO7 instantiation: `ko7Schema`, `ko7System`, additive / transparent-compositional / affine barrier KO7 corollaries, `dpProjectionRank`.
- [Meta/Impossibility_Lemmas.lean](OperatorKO7/Meta/Impossibility_Lemmas.lean) — failed-measure catalog.
- [Meta/Conjecture_Boundary.lean](OperatorKO7/Meta/Conjecture_Boundary.lean) — no-go theorems and `GlobalOrients` framework (KO7).
- [Meta/KBO_Impossible.lean](OperatorKO7/Meta/KBO_Impossible.lean) — paper-facing renaming of `SymbolicComparatorBarrier` + concrete-trace bridge `no_kbo_orients_ko7_rec_succ_trace`.
- [Meta/ManySortedBarrierSurvival.lean](OperatorKO7/Meta/ManySortedBarrierSurvival.lean) — many-sorted first-order repackaging of the typed recursor fragment.
- [Meta/EscapeTrichotomy.lean](OperatorKO7/Meta/EscapeTrichotomy.lean) — schema-level `WrapSubtermSensitive` / `TransparentAtBase` / `NatDirectBarrierRepresentable` block plus the KO7-specific extension (`ko7_nat_direct_escape_trichotomy`, `ko7_direct_escape_trichotomy_extended`, `ko7_projection_escape_trichotomy`).

**Where Layer 8 fits.** Above Layer 1 (the barrier theorems) and feeding
both Layer 4 (via `dpProjectionRank`) and the TPDB-bridge layer.

---

## Layer 9 — KO7 global witnesses and full-step ordinations

- [Meta/PolyInterpretation_FullStep.lean](OperatorKO7/Meta/PolyInterpretation_FullStep.lean) — the nonlinear polynomial witness `W`, `W_orients_step`, `wf_StepRev_poly`, axiom-violation lemmas.
- [Meta/TTT2_CertificateReplay.lean](OperatorKO7/Meta/TTT2_CertificateReplay.lean) — narrow Lean-side replay of the FAST certificate core: SCC count, projected argument, DP-pair well-foundedness.

**Where Layer 9 fits.** Provides KO7's imported-whole witnesses that Paper A
§4.24 cites as W1 ascents.

---

## Layer 10 — META-HALT supervisory stack (Paper 2 §5–7)

Six new modules forming a self-contained supervisory layer. Approximately
1450 LOC total. All landed inside the window.

### [Meta/MetaHalt_Signatures.lean](OperatorKO7/Meta/MetaHalt_Signatures.lean) **[NEW, 226 lines, 27 declarations]**

Finite decidable signature infrastructure. `FeatureTag`, `GoalTag`,
`TraceTag` enums (all `DecidableEq`), `LanguageSignature`,
`ObligationSignature`, `SearchTraceSignature` records, `AdmissibilityRule` /
`AdmissibilityTable` with finite decidable lookup, `LoopPattern` /
`LoopPatternTable` certified-loop-pattern registry. Mechanizes Paper 2
Prop 5.4 ("META-HALT consumes signatures, not proofs").

### [Meta/MetaHalt_Predicate.lean](OperatorKO7/Meta/MetaHalt_Predicate.lean) **[NEW, 155 lines]**

The binary META-HALT predicate and typed-output taxonomy.
`MetaHaltClause` (four clauses of Paper 2 Def 5.3), `metaHalt`,
`metaHalt_consumes_signatures_not_proofs`, `TypedOutput` enum (five
categories), `isTypedOutputDisciplineViolation`,
`isFalseSupervisoryTermination`, `t4_abstention_well_formed_not_violation`,
`untyped_t4_refusal_is_violation`.

### [Meta/MetaHalt_Regress.lean](OperatorKO7/Meta/MetaHalt_Regress.lean) **[NEW, 523 lines, 17 declarations]**

Supervisory-loop machinery and termination. `SupervisoryLoopOutcome`,
`SupervisoryLoopState`, `CatalogLiftPolicy`, `InnerSearchStep`,
`supervisoryLoop`, `supervisoryLoopWithSteps` (counted companion),
`Catalog.remainingCount`, `Catalog.totalBudgetPlusOne`,
`supervisoryLoop_terminates_in_catalog_budget` (Paper 2 Prop 5.6 at
strengthened form), `supervisoryLoop_emits_c3_or_c1c2`,
`audit_entry_fields_total`.

### [Meta/MetaHalt_Soundness.lean](OperatorKO7/Meta/MetaHalt_Soundness.lean) **[NEW, 225 lines]**

Catalog soundness and below-threshold safety. `catalogSound`,
`catalogComplete`, `metaHalt_is_catalog_sound`,
`no_c1_c2_from_blocked_class` (Paper 2 Lem 5.16),
`below_threshold_only_c3_or_lift`, `below_threshold_forces_metahalt`
(Paper 2 Prop 5.33), `catalogSound_suffices_for_safety` (Paper 2
Principle 5.15).

### [Meta/MetaHalt_Fracture.lean](OperatorKO7/Meta/MetaHalt_Fracture.lean) **[NEW, 261 lines, 10 declarations]**

Pre-Undecidability Fracture Theorem and FLC. `OperationTag`,
`taskRequiredOperations`, `OperationsPerformed`, `exhaustionGap`,
`exhaustionGap_zero_iff_all_performed`, `no_c4_above_nonzero_gap`
(exhaustion-gap-hypothesis form, not all-false licensing),
`pre_undecidability_fracture` (Paper 2 Thm 6.1 via `supervisoryLoop`
outcomes and `below_threshold_forces_metahalt`),
`FaultLineCompleteArchitecture`, `flc_layers_necessary_witness_transition`,
`flc_layers_necessary_meta_halt` (Paper 2 Prop 7.2).

### [Meta/MetaHalt_PaperInterface.lean](OperatorKO7/Meta/MetaHalt_PaperInterface.lean) **[NEW, 58 lines]**

Paper-facing alias layer mapping META-HALT Lean identifiers to Paper 2's
Theorem / Proposition / Definition labels.

**Where Layer 10 fits.** Imports Layer 3 (`WitnessOrder`,
`OperationalIncompleteness`), Layer 4 (confession-method family for T3
output type), Layer 11 (structural minimality for the fracture theorem's
hypothesis). Produces Paper 2 §5–7 in mechanized form end-to-end.

---

## Layer 11 — Structural minimality and boundary factorization

### [Meta/BenchmarkedPrimitiveRecursionFamily.lean](OperatorKO7/Meta/BenchmarkedPrimitiveRecursionFamily.lean) (352 lines, 27 declarations)

Paper 2 Thm 5.4 at full theorem strength. `BaseRuleFlag`, `StepRuleFlag`,
`PRCConfig` (six-member family), `fullLinear` / `fullDuplicating`,
`StructurallyComplete`, `FamilyStep`, `FamilyCallStep`, three witness
predicates, the explicit `directAdditiveWitness` for non-duplicating
members, four direct-witness theorems, three no-direct-witness theorems,
four imported / transformed-call witness theorems,
`global_family_classification`,
`fullDuplicating_unique_blocked_complete_member` (uniqueness biconditional),
`every_other_complete_member_has_direct_witness`,
`fullDuplicating_is_global_minimum_in_bench_family`.

### [Meta/BoundaryFactorization.lean](OperatorKO7/Meta/BoundaryFactorization.lean) (97 lines, 5 theorems)

Three ablation facts. `recursion_alone_not_sufficient_for_barrier`,
`simple_typing_not_escape_mechanism_additive`,
`simple_typing_not_escape_mechanism_affine`,
`sharing_can_break_tree_barrier`, `ko7_barrier_is_duplication`.

**Where Layer 11 fits.** Uses Layer 8's KO7 barrier infrastructure plus the
typed / sharing ablations. Supplies the inputs to Layer 10's fracture
theorem and to Paper 2 §5's structural-minimality argument.

---

## Layer 12 — KO7 operational incompleteness and witness order (Paper 2 bridge)

### [Meta/WitnessOrder.lean](OperatorKO7/Meta/WitnessOrder.lean) (247 lines)

KO7-specific witness tower. `WLevel`, `WitnessTower`, `HasWitness`,
`kappaLe`, `kappaGt`, `TaskContract`, `contractTower`,
`benchmarkContract`, `DirectWholeWitness`, `ko7Tower` and all the `ko7_*`
witness theorems connecting KO7 to Paper 2's witness-order threshold.

### [Meta/OperationalIncompleteness.lean](OperatorKO7/Meta/OperationalIncompleteness.lean) (145 lines)

KO7-specific operational incompleteness. `CertifiedForgettingWitness`
(KO7 `Trace`), `dpCertifiedForgettingWitness`, `ko7CarrierEquivTrace`
(explicit type equivalence between `ko7Schema.T` and `Trace`),
`CertifiedForgettingWitness.ofConfessionMethod` (lifts any KO7
confession method to a certified forgetting witness),
`PayloadOperationalIncompleteness`, `ko7PayloadOperationalIncompleteness`,
`ko7_admissible_witness_requires_certified_forgetting`,
`dp_projection_exhibits_certified_forgetting`.

**Where Layer 12 fits.** Sits between Layer 0 (uses `ko7Schema`) and Layer 10
(fed into the META-HALT fracture theorem). Supplies the KO7-facing bridges
that Paper 2 §5 cites.

---

## Layer 13 — Textbook second instance

### [Meta/TextbookDupInstance.lean](OperatorKO7/Meta/TextbookDupInstance.lean)

Second named schema instance for the classical rule
`f(x, s(y)) → g(x, f(x, y))`. Defines `TextbookTerm` inductively, builds
`textbookSchema : StepDuplicatingSchema`, and exposes direct additive,
transparent-compositional, and affine barrier corollaries plus specialized
witness-extractor aliases. Supports Paper A Remark 4.3's claim that "the
reusable boundary layer applies to a second named duplicating TRS, not
only to KO7".

---

## Layer 14 — Public API and tests

### [OperatorKO7/SchemaAPI.lean](OperatorKO7/SchemaAPI.lean)

The stable public entry point. Over the window it grew to re-export:

- Core schema and free-syntax layer (`StepDuplicatingSchema`,
  `FreeStepDuplicatingSyntax`).
- Twelve direct barrier families plus tropical / depth / affine-threshold
  continuations.
- Vector / matrix-side barriers including arbitrary-dimension lex and
  permutation-priority lex.
- Symbolic / KBO, pumped subclasses, standard pump lemmas.
- Second schema instance (`TextbookDupInstance`).
- Executable boundary tooling (witness extractors, budgets, synthesis
  oracle, barrier classifier).
- Confession-method family (`_DP`, `_CounterProjection`, `_SCT`,
  `_ArgumentFiltering`, `_Family`, `_Unification`).
- DP fragment.
- Graph / SCC extraction utilities.
- Delayed-duplication and preserving-SCC families with their abstract,
  relational, call-graph, and extracted-call-graph layers.
- Cross-paper schema interfaces (`BenchmarkedPrimitiveRecursionFamily`,
  `OperationalIncompleteness`).
- Paper 2 Layer 2 quantitative / diagnostic modules plus Layer 3
  forgetting-witness, operational-incompleteness, witness-order.

### [OperatorKO7/OperatorKO7.lean](OperatorKO7/OperatorKO7.lean)

The library root. Refreshed to import everything (including the META-HALT
layer and the free-syntax bridge).

### [Test/SchemaAPIReach.lean](OperatorKO7/Test/SchemaAPIReach.lean) **[NEW]**

Reachability smoke test for `SchemaAPI.lean`. Touches a representative
symbol from every re-exported block so that any accidental import drop
surfaces immediately as an elaboration error.

### [Test/MetaHalt.lean](OperatorKO7/Test/MetaHalt.lean) **[NEW, 40 lines]**

Reachability smoke test for the META-HALT layer.

**Where Layer 14 fits.** At the top of the import DAG. `SchemaAPI.lean`
is the narrow entry for downstream consumers; `OperatorKO7.lean` is the
full library root.

---

## Layer 15 — Scripts

### [scripts/validate_manuscript_refs.py](scripts/validate_manuscript_refs.py) **[NEW, 222 lines]**

Standalone `\path{...}` validator for the private manuscripts. Two checks:
file / module references resolve to an existing repository path;
declaration-style references occur textually in the Lean sources. Runs
locally because the manuscripts are in a sibling private tree.

### [scripts/make_referee_bundle.py](scripts/make_referee_bundle.py)

Referee-bundle writer (modified in the window).

### [scripts/stage_tpdb_submission.py](scripts/stage_tpdb_submission.py)

Staged TPDB submission helper (modified).

### [generate_docs.py](generate_docs.py)

Regenerates `OperatorKO7_Complete_Documentation.md` from all `.lean`
sources (modified).

---

## Layer 16 — Documentation

### New in the window

- [Docs/META_HALT_EXECUTION_BIBLE.md](Docs/META_HALT_EXECUTION_BIBLE.md) — 2518 lines, line-by-line implementation instructions for the META-HALT Lean agent.
- [Docs/META_HALT_FORMALIZATION_PLAN.md](Docs/META_HALT_FORMALIZATION_PLAN.md) — 256 lines, architectural overview and target-content table.
- [Docs/META_HALT_PROGRESS.md](Docs/META_HALT_PROGRESS.md) — 22 lines, daily status log; the April 15 entry records the repair-pass closure of all five load-bearing META-HALT theorems.
- [Docs/S165_PUBLIC_API_NOTE.md](Docs/S165_PUBLIC_API_NOTE.md) — public-API boundary note for `SchemaAPI.lean`.

### Modified in the window

- [Docs/KO7_BLUEPRINT.md](Docs/KO7_BLUEPRINT.md) — bidirectional proof-dependency graph (human-readable).
- [Docs/ko7_blueprint.json](Docs/ko7_blueprint.json) — same graph, JSON.
- [Docs/Impossibility_DeadEnds.md](Docs/Impossibility_DeadEnds.md).
- [Artifacts/MICRO_BENCHMARKS.md](Artifacts/MICRO_BENCHMARKS.md).
- [Artifacts/REPRODUCIBILITY.md](Artifacts/REPRODUCIBILITY.md).
- [Artifacts/ttt2/README.md](Artifacts/ttt2/README.md).

### Repo-root reports (all new in the window)

- [blueprint-04-14-2026.md](blueprint-04-14-2026.md) — April 14 confession-sprint blueprint (historical).
- [confession-method-implementation-report-04-14-2026.md](confession-method-implementation-report-04-14-2026.md) — companion implementation report (historical).
- [SCHEMA_GAP_ROADMAP.md](SCHEMA_GAP_ROADMAP.md) — live work ledger for schema boundary.
- [new_additions.md](new_additions.md) — this file.

---

## Appendix A — Brand-new files (first landed inside the window)

21 files. Ordered by layer.

1. `Meta/FreeStepDuplicatingSyntax.lean` (Layer 0)
2. `Meta/FreeStepDuplicatingTraceBridge.lean` (Layer 0)
3. `Meta/SchemaCanonicalTrace.lean` (Layer 2)
4. `Meta/SchemaOffsetAndWrapper.lean` (Layer 2)
5. `Meta/SchemaConfessionDominance.lean` (Layer 2)
6. `Meta/SchemaNormMismatch.lean` (Layer 2)
7. `Meta/SchemaSeedCarrierFactorization.lean` (Layer 2)
8. `Meta/SchemaForgettingWitness.lean` (Layer 3)
9. `Meta/SchemaWitnessOrder.lean` (Layer 3)
10. `Meta/SchemaOperationalIncompleteness.lean` (Layer 3)
11. `Meta/ConfessionMethod_Unification.lean` (Layer 4)
12. `Meta/MetaHalt_Signatures.lean` (Layer 10)
13. `Meta/MetaHalt_Predicate.lean` (Layer 10)
14. `Meta/MetaHalt_Regress.lean` (Layer 10)
15. `Meta/MetaHalt_Soundness.lean` (Layer 10)
16. `Meta/MetaHalt_Fracture.lean` (Layer 10)
17. `Meta/MetaHalt_PaperInterface.lean` (Layer 10)
18. `Test/SchemaAPIReach.lean` (Layer 14)
19. `Test/MetaHalt.lean` (Layer 14)
20. `scripts/validate_manuscript_refs.py` (Layer 15)
21. `Docs/META_HALT_EXECUTION_BIBLE.md`, `Docs/META_HALT_FORMALIZATION_PLAN.md`,
    `Docs/META_HALT_PROGRESS.md`, `Docs/S165_PUBLIC_API_NOTE.md` (Layer 16)

---

## Appendix B — Substantively modified files

71 files. Grouped by layer.

**Layer 0 (schema core):** `StepDuplicatingSchema.lean`.

**Layer 1 (direct barriers):** `QuadraticBarrier.lean`,
`WPO_PolynomialBarrier.lean`, `MatrixBarrierLexD.lean`,
`MatrixBarrierLexPermD.lean`, `ProjectedPrimaryBarrier.lean`,
`DepthBarrier.lean`.

**Layer 4 (confession family):** `ConfessionMethod.lean`,
`ConfessionMethod_DP.lean`, `ConfessionMethod_CounterProjection.lean`,
`ConfessionMethod_SCT.lean`, `ConfessionMethod_ArgumentFiltering.lean`,
`ConfessionMethod_Family.lean`.

**Layer 5 (SCC extensions):** `MutualDuplication_General.lean`,
`MutualDuplication_CycleFlow.lean`, `MutualDuplication_KNode.lean`,
`MutualDuplication_KNode_Abstract.lean`,
`MutualDuplication_GraphCycle.lean`,
`MutualDuplication_Transparent.lean`,
`MutualDuplication_PayloadFlow.lean`,
`MutualDuplication_Preserving.lean`,
`MutualDuplication_Preserving_KNode.lean`,
`MutualDuplication_Preserving_Abstract.lean`,
`MutualDuplication_Preserving_Transparent.lean`,
`MutualDuplication_PacketGraph.lean`,
`MutualDuplication_RelationalGraph.lean`,
`MutualDuplication_CallGraph.lean`,
`MutualDuplication_ExtractedCallGraph.lean`,
`GraphPathExtraction.lean`, `FiniteGraphReachability.lean`,
`FiniteGraphSCC.lean`.

**Layer 6 (DP extraction):** `DependencyPairs_FiniteGraph.lean`,
`DependencyPairs_CallGraph.lean`,
`DependencyPairs_ExtractedCallGraph.lean`,
`DependencyPairs_TPDBExtraction.lean`,
`DependencyPairs_FirstOrderExtraction.lean`,
`DependencyPairs_FirstOrderFrontend.lean`,
`DependencyPairs_FirstOrderEngine.lean`,
`DependencyPairs_HeadView.lean`,
`DependencyPairs_FiniteCarrierView.lean`,
`DependencyPairs_KernelFirstOrder.lean`.

**Layer 7 (complexity / confluence / ordinal):**
`ContextualCopyBudget.lean`, `ContextualCopyBudget_NoGo.lean`,
`SafeStepCtx_Complexity_Exponential.lean`,
`SafeStepCtx_Complexity_LowerBound.lean`,
`SafeStepCtx_Complexity_Cichon.lean`,
`SafeStep_Complexity_Ordinal.lean`,
`SafeStep_Complexity_MW_Root.lean`,
`SafeStep_Complexity_MW_Ctx.lean`,
`SafeStep_Complexity_MW_CtxExact.lean`,
`SafeRoot_Complexity.lean`, `Reachability_Complexity.lean`,
`SafeStepCtx_Confluence.lean`, `Newman_Safe.lean`,
`DM_OrderType.lean`, `DM_UpstreamSurface.lean`,
`Mu3c_Image_LowerBound.lean`.

**Layer 8 (certified measure / KO7 barrier instantiation):**
`ComputableMeasure.lean`, `ComputableMeasure_Verification.lean`,
`BarrierWitness.lean`, `BarrierWitness_Budgets.lean`,
`CompositionalMeasure_Impossibility.lean`,
`Impossibility_Lemmas.lean`, `Conjecture_Boundary.lean`,
`KBO_Impossible.lean`, `ManySortedBarrierSurvival.lean`,
`EscapeTrichotomy.lean`.

**Layer 9 (KO7 global witnesses):**
`PolyInterpretation_FullStep.lean`, `TTT2_CertificateReplay.lean`.

**Layer 11 (structural minimality):**
`BenchmarkedPrimitiveRecursionFamily.lean`,
`BoundaryFactorization.lean`.

**Layer 12 (KO7 OI / witness order):** `WitnessOrder.lean`,
`OperationalIncompleteness.lean`.

**Layer 13 (textbook instance):** `TextbookDupInstance.lean`.

**Layer 14 (API):** `SchemaAPI.lean`, `OperatorKO7.lean`.

**Layer 15 (scripts):** `scripts/make_referee_bundle.py`,
`scripts/stage_tpdb_submission.py`, `generate_docs.py`.

---

## Appendix C — Verification

- `lake build OperatorKO7` — green.
- `lake build` (full library root) — green.
- `pdflatex Rahnama_The_Orientation_Boundary.tex` — 57 pages, no errors, no undefined references.
- `lake env lean OperatorKO7/Test/SchemaAPIReach.lean` — passes.
- `lake env lean OperatorKO7/Test/MetaHalt.lean` — passes.
- `scripts/validate_manuscript_refs.py` — passes against Paper A (April 15).
- `#print axioms` on headline declarations: only `propext`, `Classical.choice`, `Quot.sound`.

---

## Appendix D — Theorem-stack diagram

The layer numbers above reflect the import DAG. Bottom-to-top:

```
  ┌─ Layer 0  Schema core  ──┬── FreeStepDuplicatingSyntax
  │  StepDuplicatingSchema   ├── FreeStepDuplicatingTraceBridge
  │                          └── (imports nothing in this tree)
  │
  ├─ Layer 1  Direct barriers (twelve families + depth + projected primary)
  │                          (↓ imports Layer 0)
  │
  ├─ Layer 2  Paper 2 §3 diagnostic / quantitative
  │    SchemaCanonicalTrace → SchemaOffsetAndWrapper →
  │    SchemaConfessionDominance → SchemaNormMismatch →
  │    SchemaSeedCarrierFactorization
  │                          (↓ imports Layer 0 and Layer 1's base-duplicating system)
  │
  ├─ Layer 3  Forgetting witness + schema OI + witness order (Paper 2 §4–5)
  │    SchemaForgettingWitness → SchemaOperationalIncompleteness
  │    SchemaWitnessOrder
  │                          (↓ imports Layers 0, 1, 2)
  │
  ├─ Layer 4  Confession-method family + unification
  │    ConfessionMethod → ConfessionMethod_{DP,CP,SCT,AF}
  │    → ConfessionMethod_Family → ConfessionMethod_Unification
  │                          (↓ imports Layer 0, Layer 3)
  │
  ├─ Layer 5  SCC extensions (delayed, preserving, graph-based)
  │                          (↓ imports Layer 0)
  │
  ├─ Layer 6  DP extraction tooling
  │                          (↓ imports Layer 0, Layer 4 fragments)
  │
  ├─ Layer 7  Complexity, confluence, ordinal calibration
  │                          (↓ imports Layer 0 + KO7 kernel)
  │
  ├─ Layer 8  Certified measure / KO7 instantiation / escape trichotomy
  │                          (↓ imports Layers 0–2, 7)
  │
  ├─ Layer 9  KO7 global witnesses (W, MPO, TTT2 replay)
  │                          (↓ imports Layer 8)
  │
  ├─ Layer 10 META-HALT supervisory stack (Paper 2 §5–7)
  │    MetaHalt_Signatures → _Predicate → _Regress → _Soundness →
  │    _Fracture → _PaperInterface
  │                          (↓ imports Layers 3, 11, 12)
  │
  ├─ Layer 11 Structural minimality (PRC family) + boundary factorization
  │                          (↓ imports Layer 8)
  │
  ├─ Layer 12 KO7 OI + witness order (cross-paper bridge)
  │                          (↓ imports Layers 4, 8)
  │
  ├─ Layer 13 Textbook second instance
  │                          (↓ imports Layer 0 + Layer 1)
  │
  └─ Layer 14 Public API surfaces (SchemaAPI, OperatorKO7) + tests
```

Above Layer 14 sit the Python scripts (Layer 15) and `Docs/` files
(Layer 16), which treat the Lean tree as input data rather than importing
it.

---

## Appendix E — Paper-wise correspondence

### Paper A (`Rahnama_The_Orientation_Boundary.tex`)

- §3 "Canonical trace, trace coordinates, and wrapper stack" → Layer 2.
- §4 barrier stack → Layer 1 + Layer 5 + Layer 8.
- §4.10 "The DP escape" + forgetting-witness proposition → Layer 3 + Layer 4 + Layer 12.
- §5 "Schema-level diagnostic layer" → Layer 2 + Layer 3.
- §5 certification chain → Layer 7 + Layer 9.
- §6 TTT2 / CeTA → Layer 9.
- Addendum module map → Layers 0–12 collectively.
- Addendum claim-to-code → individual theorem identifiers across all layers.

### Paper 2 (`Rahnama_The_Failure_Floor_Beneath_Impossibility.tex`)

- §3 quantitative trace layer → Layer 2.
- §4 witness-order → Layer 3 (`SchemaWitnessOrder`) + Layer 12 (`WitnessOrder`).
- §5 operational incompleteness → Layer 3 + Layer 12.
- §5 structural minimality (Thm 5.4) → Layer 11.
- §5 construction / confession asymmetry → Layer 3.
- §5 confession family (the W2 remark) → Layer 4 + Layer 12.
- §5 supervisory predicate + regress → Layer 10 (`_Signatures`, `_Predicate`, `_Regress`, `_Soundness`).
- §6 Pre-Undecidability Fracture Theorem → Layer 10 (`_Fracture`).
- §7 FLC necessary layers → Layer 10 (`_Fracture`).
- §5.11 / 5.12 / 5.13 / 5.14 / 5.15 — explicitly marked open by Paper 2; not mechanized.
- §2 information-theoretic preliminaries — not yet mechanized (scope decision pending).

---

## Appendix F — What is closed versus what remains

### Closed in the window

- Eight Paper 2 §3 quantitative modules (Layer 2).
- Three Paper 2 §4–5 abstraction modules (Layer 3).
- One unification layer + five semantic-profile theorems across the confession family (Layer 4).
- Five convergence formulations at strictly increasing abstraction: rank, projection, confession-core, semantic profile, extended-profile uniqueness on KO7 (Layers 0 + 4 together).
- One canonical generated-schema instance (`FreeStepDuplicatingSyntax`) plus its KO7 bridge (`FreeStepDuplicatingTraceBridge`).
- Six-module META-HALT stack including the Pre-Undecidability Fracture Theorem (Layer 10).
- `MaxDepthMeasure` schema lift (Layer 1).
- `SafeStepCtx_Confluence` unconditional confluence (Layer 7).
- `SafeStepCtx_Complexity_LowerBound` explicit exponential lower family (Layer 7).
- `SafeStep_Complexity_MW_CtxExact` direct exact contextual extraction (Layer 7).
- Paper A §3 canonical-trace subsection, §4 forgetting-witness proposition, §5 schema-level diagnostic layer, Addendum module map and claim-to-code table.
- `validate_manuscript_refs.py` citation-drift canary.
- P1 unused-import cleanup (`ConfessionMethod.lean`).

### Remaining

- Three-root public API split (`PrimitiveSchemaAPI` / `SchemaExtendedAPI` / `CrossPaperAPI`). Architectural decision pending.
- Schema-half extraction of `EscapeTrichotomy` into a dedicated file. Pending.
- Paper 2 §2 information-theoretic preliminaries. Scope decision pending.
- Paper 2 Thm 5.11 Gödel 6-step structural identity; Prop 5.12 not-diagonal; Prop 5.13 reflection-family; Prop 5.14 AG-Π⁰₂; Conj 5.15 AG-RCA₀. Paper 2 itself marks these as open / prose-only.
- Mixed schema/KO7 file-purity question.
- DP extraction stack public-API decision.
- Documentation reconciliation of the two April 14 reports against the current stronger code.

---

## Bottom line

One month of work produced 21 genuinely new Lean modules and rewrote or
extended 71 existing ones. The confession-method family moved from alias-
level provenance to a five-level convergence theorem (rank → projection →
core-witness → semantic profile → extended-profile uniqueness on KO7), with
a concrete free-syntax instance and a KO7 `Trace` bridge certifying that
the confession ranks literally factor through the primitive fragment.
Paper 2 §3 (quantitative trace), §4 (witness-order threshold), and §5–7
(operational incompleteness, construction/confession, canonical instance,
structural minimality, construction-confession exclusivity, projection
transaction, supervisory predicate, regress termination, soundness,
Pre-Undecidability Fracture, FLC necessary layers) are mechanized end to
end, modulo the items Paper 2 itself marks open. Paper A cites every new
Lean result through §3 canonical-trace, §4 forgetting-witness, §5
schema-level diagnostic layer, Addendum module map, and claim-to-code
table. Build, tests, axiom spot-checks, and manuscript-ref validation all
pass.
