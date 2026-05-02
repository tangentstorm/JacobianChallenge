# Top-Down Comparator Plan

This file augments the bottom-up plan in `ref/plan.md`,
`Jacobian/WorkPackets/StatementBank.lean`, and `aristotle_tasks.md`.
It is written for Claude timer ticks. The goal is to make
`Jacobian/Solution.lean` into a top-down refinement of
`Jacobian/Challenge.lean`, while Aristotle continues to work on small
bottom-up proof packets.

## Purpose

`Jacobian/Challenge.lean` is the frozen public specification. Do not edit it
unless the human explicitly asks.

`Jacobian/Solution.lean` is the top-down refinement target. It should stay
independent of `Jacobian/Challenge.lean`: both files import a trusted prelude
and declare the same public names, and comparator checks externally that the
solution proves the same statements as the challenge.

The top-down lane has two jobs:

1. Replace each top-level `sorry` in `Solution.lean` by a named analytic
   construction or theorem.
2. When a construction is still missing, expose that missing piece as a precise
   helper declaration in a production module or narrow work-packet file.

This deliberately moves `sorry`s downward. The number of top-level `sorry`s in
`Solution.lean` should shrink over time, while named lower-level obligations
become Aristotle-sized tasks.

## Comparator Role

Use `leanprover/comparator` to compare the trusted challenge module with the
solution module.

Canonical comparator shape:

```json
{
  "challenge_module": "Jacobian.Challenge",
  "solution_module": "Jacobian.Solution",
  "theorem_names": [
    "genus_eq_zero_iff_homeo",
    "Jacobian.ofCurve_contMDiff",
    "Jacobian.ofCurve_self",
    "Jacobian.ofCurve_inj",
    "Jacobian.pushforward_contMDiff",
    "Jacobian.pushforward_id_apply",
    "Jacobian.pushforward_comp_apply",
    "Jacobian.pullback_contMDiff",
    "Jacobian.pullback_id_apply",
    "Jacobian.pullback_comp_apply",
    "Jacobian.pushforward_pullback"
  ],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
  "enable_nanoda": false
}
```

First smoke test: determine whether comparator should also list data
declarations such as `genus`, `Jacobian`, `Jacobian.ofCurve`,
`Jacobian.pushforward`, `Jacobian.pullback`, and `ContMDiff.degree`, or whether
it should be used only for theorem/lemma declarations. Until that is checked,
use comparator for theorem-surface equivalence and ordinary Lean builds for
data-signature sanity.

Do not make `Solution.lean` import `Challenge.lean`. That defeats the purpose of
the independent comparison.

## Current Production Layers

The useful solution bank is no longer just `StatementBank.lean`; it is the
production module hierarchy:

- `Jacobian.ComplexTorus`: quotient complex torus infrastructure, including
  quotient group/topology, charted space, manifold, projection smoothness,
  addition/negation smoothness, and `LieAddGroup`.
- `Jacobian.HolomorphicForms`: current holomorphic-form skeleton, analytic
  genus, evaluation maps, extensionality, and finite-dimensional witness API.
- `Jacobian.Periods`: path/chart integration scaffolding, period pairing API,
  period subgroup closure/arithmetic, with the deepest period pairing
  construction still intentionally opaque.
- `Jacobian.AnalyticJacobian`: abstract quotient-group Jacobian skeleton and
  algebra around `mk`, period-pairing classes, and equality criteria.
- `Jacobian.AbelJacobi`: witness-level Abel-Jacobi algebra, base change,
  telescoping, nontriviality, and vanishing criteria.
- `Jacobian.TraceDegree`: pullback-form and trace/degree algebra skeletons.

Before adding a new top-down helper, check whether a production module already
has the right theorem under a slightly different name.

## Mathematical Spine

The intended top-down construction is:

```text
HolomorphicOneForm X
  -> finite-dimensionality
  -> genus X

IntegralOneCycle X
  -> periodPairing
  -> periodSubgroup
  -> periodFullComplexLattice

HolomorphicOneFormDual X / period lattice
  -> Jacobian X
  -> compact complex Lie additive group

pathIntegralFunctional P Q
  -> Jacobian.ofCurve P Q

pullbackForms / traceForms / analyticDegree
  -> Jacobian.pullback / Jacobian.pushforward / ContMDiff.degree
  -> pushforward_pullback
```

Top-down work should preserve this spine. Avoid introducing a fake abstraction
that makes the challenge compile but has no path back to the period-lattice
construction.

## Refinement Order

Work in small rounds. Each round should replace one cluster of top-level
`sorry`s in `Solution.lean` with named lower-level declarations.

### Round 0: Comparator Harness ✅

Done (2026-04-27). Configs live under `comparator/`:

- `comparator/jacobian.json` — final config, axioms `propext / Quot.sound /
  Classical.choice` only.
- `comparator/jacobian-staged.json` — staged-refinement variant adding
  `sorryAx` so comparator accepts shape-equivalence while bottom-up
  obligations are still in flight.
- `comparator/README.md` — usage notes plus the **known data-level
  universe divergence** introduced by the keystone refactor (Solution's
  `Jacobian X : Type` vs Challenge's `Jacobian X : Type u`), root-caused
  to Mathlib's `HasCoproducts.{w} (ModuleCat ℤ)` only being at `w = 0`,
  with three documented paths to repair.

The smoke test itself is deferred until either the comparator binary is
installed locally or one of the universe-repair paths lands.

Theorem-name list contains theorem-level declarations only (matches the
canonical config above). Decision on whether data declarations
(`genus`, `Jacobian`, etc.) should be included is deferred — the
universe-divergence issue must be settled first since it would
trivially fail any data-level check today.

### Round 1: Genus

Target declarations:

- `genus`
- `genus_eq_zero_iff_homeo`

Desired refinement:

```text
genus X := analyticGenus X
genus_eq_zero_iff_homeo := analytic genus zero classification theorem
```

Likely helper obligations:

- real `HolomorphicOneForm` definition for compact Riemann surfaces;
- `FiniteDimensional ℂ (HolomorphicOneForm X)`;
- classification theorem:
  `analyticGenus X = 0 <-> X ≃ₜ sphere`.

This is mathematically deep. It is fine for the top-down file to expose this as
a named theorem obligation, but do not ask Aristotle to prove the whole
classification theorem in one job.

### Round 2: Jacobian Type And Basic Instances

Target declarations:

- `Jacobian`
- `AddCommGroup (Jacobian X)`
- `TopologicalSpace (Jacobian X)`
- `T2Space (Jacobian X)`
- `CompactSpace (Jacobian X)`
- `ChartedSpace (Fin (genus X) -> ℂ) (Jacobian X)`
- `IsManifold ... (Jacobian X)`
- `LieAddGroup ... (Jacobian X)`

Desired refinement:

```text
Jacobian X := transported analytic period quotient
```

The period quotient should be built from:

```text
HolomorphicOneFormDual X / periodFullComplexLattice X
```

Use `Jacobian.ComplexTorus` for the quotient torus instances. The main design
work is not the quotient torus anymore; it is the bridge from the actual period
subgroup to a `FullComplexLattice` and the universe/model transport from the
analytic quotient to the challenge's `Type u` and `Fin (genus X) -> ℂ` model.

Likely helper obligations:

- `periodFullComplexLattice X`;
- finite-dimensional model equivalence
  `HolomorphicOneFormDual X ≃L[ℂ] (Fin (genus X) -> ℂ)`;
- additive/topological/manifold transport lemmas;
- explicit universe bridge, probably via `ULift` or a chosen finite model.

### Round 3: Abel-Jacobi Map

Target declarations:

- `Jacobian.ofCurve`
- `Jacobian.ofCurve_contMDiff`
- `Jacobian.ofCurve_self`
- `Jacobian.ofCurve_inj`

Desired refinement:

```text
ofCurve P Q := class of (ω |-> integral from P to Q of ω)
```

Likely helper obligations:

- path integral functional from a base point to an endpoint;
- path-independence modulo the period subgroup;
- base-point integral is zero;
- holomorphicity of the Abel-Jacobi map;
- injectivity for positive genus.

`ofCurve_inj` is a major anti-hack theorem. Treat it as its own theorem-level
project. Do not collapse it into a broad opaque "Abel-Jacobi works" axiom unless
the declaration name and mathematical dependency are explicit.

### Round 4: Pullback, Pushforward, Degree

Target declarations:

- `Jacobian.pushforward`
- `Jacobian.pullback`
- `ContMDiff.degree`
- `pushforward_contMDiff`
- `pullback_contMDiff`
- identity and composition lemmas for pushforward/pullback
- `pushforward_pullback`

Desired refinement:

```text
pullback: dual of pullback of holomorphic forms, descending through periods
pushforward: trace on holomorphic forms or equivalent homological pushforward
degree: analytic/geometric degree of a holomorphic map
pushforward_pullback: trace_f (pullback_f ω) = degree(f) • ω
```

Likely helper obligations:

- smooth pullback of holomorphic 1-forms;
- trace map on holomorphic 1-forms;
- preservation of period lattices;
- functoriality of the induced quotient maps;
- analytic degree and composition laws;
- trace-pullback identity.

Aristotle can help with the algebraic quotient-map and linear-map consequences
once Claude states the trace/pullback assumptions precisely. Aristotle should
not be asked to invent the degree theory globally.

## Claude / Aristotle Division

Claude owns:

- editing `Solution.lean`;
- choosing public helper theorem names;
- deciding when a top-level `sorry` has been refined enough to move downward;
- maintaining this file, `ref/plan.md`, `aristotle_tasks.md`, and any comparator
  config;
- integrating production-module results into the top-down bridge.

Aristotle owns:

- one theorem family in one target file;
- proof-only tasks after statements are fixed;
- algebraic consequences of already-defined constructions;
- blocker reports naming missing prerequisites.

Good Aristotle tasks:

- prove a transport lemma between an analytic quotient and a challenge-facing
  wrapper type;
- prove quotient-map functoriality from a lattice-preserving linear map;
- prove pullback-form algebra after `pullbackFormsFun` is defined;
- prove path-integral linearity/congruence lemmas in a fixed chart;
- prove a small period-subgroup membership lemma.

Bad Aristotle tasks:

- "make `Solution.lean` pass comparator";
- "define the Jacobian";
- "prove Abel-Jacobi injectivity";
- "prove genus zero classification";
- "formalize all degree theory".

## Tick Cadence

Use alternating emphasis, not a hard rule:

```text
Top-down tick:
  - inspect `Solution.lean` and this file;
  - refine one top-level declaration or theorem cluster;
  - expose the missing helper obligations with stable names;
  - update this document or `aristotle_tasks.md` if new jobs are created.

Bottom-up tick:
  - pick one exposed helper obligation;
  - solve it locally or submit an Aristotle job with disjoint write scope;
  - integrate only narrow returned patches;
  - wire successful results into the relevant umbrella module.
```

Do not let `StatementBank.lean` become a parallel implementation substrate.
When a helper becomes real infrastructure, put it in the appropriate production
module and let `StatementBank.lean` remain a mirror/index if needed.

## Declaration Map

This table is the current top-down bridge inventory. Keep it updated as
`Solution.lean` changes.

| Challenge declaration | Intended solution source | Main missing bridge |
| --- | --- | --- |
| `genus` ✅ refined | `HolomorphicForms.analyticGenus` | FD instance — `compactRiemannSurface_finiteDimensionalHolomorphicOneForms` (named sorry in `Jacobian.HolomorphicForms.CompactRiemannSurface`) |
| `genus_eq_zero_iff_homeo` ✅ refined | `analyticGenus_eq_zero_iff_homeomorphic_sphere` (assembly, no own sorry) | `analyticGenus_eq_zero_of_homeomorphic_sphere` (mp) is split through the `OnePoint ℂ` holomorphic-form computation; `holomorphicOneForm_coeff_entire` now assembles from identity-chart leaves `holomorphicOneFormIdentityChartCoeffContDiff` and `holomorphicOneForm_coeff_eq_identityChartCoeff`; `holomorphicOneForm_coeff_tendsto_zero` now assembles from inversion-chart leaves `holomorphicOneFormInversionCoeffContinuousAtZero`, `holomorphicOneForm_inversionCoeff_eq_inversionChartCoeff`, `holomorphicOneForm_identityInversionTransition_eventually`, and `holomorphicOneFormCoeffTendstoZeroOfTransition`; `holomorphicOneForm_onePointCx_toFun_infty_eq_zero` uses the real punctured-chart lemma plus theorem leaf `holomorphicOneForm_infty_vanishing_of_inversionCoeff`; the homeomorphic-sphere vanishing leaf is theorem leaf `homeoSphereHolomorphicOneFormVanishing`. The hard direction now uses a production Riemann-surface substrate: `Divisor`, `Meromorphic`, `RiemannRoch`, and `MeromorphicDegree`. `genus_zero_homeomorph_onePointCx` delegates through `genusZero_exists_nonconstant_mem_L_point` plus `genusZero_poleDivisor_eq_point_of_nonconstant_mem_L_point`, then continuity/degree/bijectivity leaves in `MeromorphicDegree`, followed by the discharged compact-to-T2 homeomorphism assembly. |
| `Jacobian` ✅ refined | `ULift (ComplexTorus.quotient (Fin (genus X) → ℂ) periodFullComplexLattice)` | `periodFullComplexLattice` (named sorry in `Jacobian.Periods.PeriodLattice`) |
| `AddCommGroup` ✅ refined | `inferInstance` via ULift transport | (none — derived) |
| `TopologicalSpace` ✅ refined | `inferInstance` via ULift transport | (none — derived) |
| `T2Space` ✅ refined | `inferInstance` via ULift transport | depends on `periodFullComplexLattice.isClosed`; `_isDiscrete` is discharged by `periodSubgroup_isZLattice` (named theorem leaf in `Jacobian.Periods.PeriodFunctional`) |
| `CompactSpace` ✅ refined | `inferInstance` via ULift transport | `_fundamentalDomain_isCompact` and `_fundamentalDomain_covers` now both delegate to `exists_compact_periodFundamentalDomain` (single named-theorem leaf in `Jacobian.Periods.PeriodFunctional`); `periodFundamentalDomain` un-opaqued to `Classical.choose` of that existence statement; `_isDiscrete` is discharged by `periodSubgroup_isZLattice` (named theorem leaf, same module). Auxiliary leaf `periodSubgroup_spans_real` (Riemann bilinear nondegeneracy) declared but not yet wired. |
| `ChartedSpace` ✅ refined | `complexTorusULift_chartedSpace` (real proof, no own sorry; codex commit `c49cf9a`) | (none — discharged) |
| `IsManifold` ✅ refined (top-down) | `complexTorusULift_isManifold` (still sorry; HasGroupoid bookkeeping deferred) | OpenPartialHomeomorph associativity / EqOnSource bookkeeping for `Homeomorph.ulift` chart cancellation |
| `LieAddGroup` ✅ refined (top-down) | `complexTorusULift_lieAddGroup` (assembly; `complexTorusULift_contMDiff_add` now factors through down/add/up) | `complexTorusULift_contMDiff_up` and `_down` remain named transport sorries |
| `Jacobian.ofCurve` ✅ refined | `ULift.up ∘ AbelJacobi.analyticOfCurve` | `pathIntegralFunctional` (named `opaque` in `Jacobian.AbelJacobi.AnalyticOfCurveBasis`) |
| `ofCurve_contMDiff` ✅ refined | `contMDiff_uLift_up.comp analyticOfCurve_contMDiff` | `analyticOfCurve_contMDiff` and `contMDiff_uLift_up` (named sorries) |
| `ofCurve_self` ✅ refined | unfold + `pathIntegralFunctional_self` | `pathIntegralFunctional_self` (named sorry) |
| `ofCurve_inj` ✅ refined | `analyticOfCurve_injective` + `ULift.up_injective` | `pathIntegralFunctional_separates_points` (named sorry) — Abel theorem point-separation leaf |
| `pushforward` ✅ refined | bundled hom over `analyticPushforward` + `ULift.up` | `analyticPushforward` (named `opaque` in `Jacobian.TraceDegree.PushforwardBasis`) |
| `pushforward_contMDiff` ✅ refined | `contMDiff_uLift_up.comp (analyticPushforward_contMDiff.comp contMDiff_uLift_down)` | `analyticPushforward_contMDiff` (named sorry) |
| `pushforward_id_apply` ✅ refined | unfold + `analyticPushforward_id_apply` | `analyticPushforward_id_apply` (named sorry) |
| `pushforward_comp_apply` ✅ refined | unfold + `analyticPushforward_comp_apply` | `analyticPushforward_comp_apply` (named sorry) |
| `pullback` ✅ refined | bundled hom over `analyticPullback` + `ULift.up` | `analyticPullback` (named `opaque` in `Jacobian.TraceDegree.PullbackBasis`) |
| `pullback_contMDiff` ✅ refined | `contMDiff_uLift_up.comp (analyticPullback_contMDiff.comp contMDiff_uLift_down)` | `analyticPullback_contMDiff` (named sorry) |
| `pullback_id_apply` ✅ refined | unfold + `analyticPullback_id_apply` | `analyticPullback_id_apply` (named sorry) |
| `pullback_comp_apply` ✅ refined | unfold + `analyticPullback_comp_apply` | `analyticPullback_comp_apply` (named sorry) |
| `ContMDiff.degree` ✅ refined | `JacobianChallenge.TraceDegree.analyticDegree` | `analyticDegree` (named `opaque` in `Jacobian.TraceDegree.AnalyticDegree`) |
| `pushforward_pullback` ✅ refined | trace–pullback identity through ULift | `analyticPushforward_analyticPullback` (named sorry — the `tr_f (f* Q) = deg(f) • Q` identity) |

## Serre-duality refinement (rounds 1–25)

Top-down expansion of `thm:serre-duality-rs` produced the file tree
under `Jacobian/HolomorphicForms/Serre/` (32 files). The public
surface in `Jacobian/HolomorphicForms/SerreDualityRS.lean` is now
refined: `RSDualizingSheaf X := RSCotangentSheaf X` (round 1) and
`serre_duality_rs` is a sorry-free assembly above
`serre_datum_for_canonical_dual_exists` + frontier `serreDualSheaf`
data (round 2). Successive rounds (3–24) decompose each named
obligation into strictly-smaller named obligations that bottom out in
Mathlib-frontier pieces (presheaves of holomorphic functions / 1-forms,
tensor product of abelian sheaves, Yoneda cup product, residue map,
harmonic-form representatives, L²-pairing nondegeneracy, line-bundle
dual / subtraction).

Externally-visible discharges:

* `h1_dualizing_sheaf_one_dim` (in `H1DualizingSheaf.lean`) is now
  sorry-free above `h1Canonical_isoToC` (round 19).
* `riemann_roch_high_degree` (in `RiemannRochHighDegree.lean`) is
  refined via `riemann_roch_high_degree_via_serre` +
  `RSLineBundleDegree_dual_tensor_canonical` + low-degree vanishing
  (round 18).
* `riemann_roch_umbrella_exists` (in
  `Blueprint/Sec02/InputRiemannRoch.lean`) is refined via
  `riemann_roch_classical_identity` (round 20).

Plan and full file inventory: `ref/plans/serre-duality-rs.md`.

## Frontier-input refinement: `input:hodge-deRham`

The blueprint big-umbrella `input:hodge-deRham` corresponds to the Lean
declaration `JacobianChallenge.Periods.hodge_deRham_rank_eq` in
`Jacobian/Periods/PeriodFunctional.lean`:

```lean
theorem hodge_deRham_rank_eq (X) [...] :
    2 * analyticGenus ℂ X = Module.finrank ℤ (IntegralOneCycle X)
```

Round (claude/expand-hodge-derham-RbzcT) refined this single `sorry` into
a multi-file frontier-obligation tree.  The body of `hodge_deRham_rank_eq`
is now a sorry-free assembly delegating to
`HolomorphicForms.two_analyticGenus_eq_finrank_intH1`.

### New helper modules

- `Jacobian/HolomorphicForms/DeRhamCohomology.lean` — opaque ℕ-valued
  dimensions `realDimDeRhamH1`, `complexDimDeRhamH1ℂ`, `realDimDeRhamH0`,
  `complexDimDeRhamH0ℂ`; frontier identities
  `realDim_deRhamH1_eq_complexDim_deRhamH1ℂ` (sorry, real-of-complex
  identification), `complexDim_deRhamH0ℂ_eq_one_of_compact_connected`
  (sorry), `realDim_deRhamH0_eq_one_of_compact_connected` (sorry).

- `Jacobian/HolomorphicForms/AntiHolomorphicOneForm.lean` — anti-holomorphic
  forms (currently aliased to `HolomorphicOneForm ℂ X` pending Mathlib
  Dolbeault decomposition); `analyticAntiGenus`,
  `analyticAntiGenus_eq_analyticGenus` (currently `rfl` under the alias),
  `AntiHolomorphicOneForm.module_finite_of_compact`,
  `AntiHolomorphicOneForm.realLinearEquiv_holomorphic`.

- `Jacobian/HolomorphicForms/HodgeStarRS.lean` — `HarmonicOneForm`
  (currently aliased to `Fin 2 → HolomorphicOneForm ℂ X`),
  `analyticHarmonicGenus`,
  `complexDim_deRhamH1_eq_analyticHarmonicGenus` (placeholder rfl),
  `analyticHarmonicGenus_eq_analyticGenus_add_anti` (sorry, Hodge
  decomposition by bidegree),
  `riemannSurface_hasGlobalConformalMetric` (placeholder),
  `analyticHarmonicGenus_finite` (sorry).

- `Jacobian/HolomorphicForms/HodgeDecomposition.lean` —
  `complexDimDeRhamH1ℂ_eq_analyticHarmonicGenus` (sorry, harmonic
  projection), `analyticHarmonicGenus_eq_two_analyticGenus` (sorry-free
  assembly), `complexDimDeRhamH1ℂ_eq_two_analyticGenus` (sorry-free
  assembly), `realDimDeRhamH1_eq_two_analyticGenus` (sorry-free
  assembly).

- `Jacobian/HolomorphicForms/DeRhamSingular.lean` — `realDimSingularH1`
  (opaque ℕ); `realDim_deRhamH1_eq_realDim_singularH1` (sorry, de Rham
  theorem on a compact smooth manifold);
  `realDim_singularH1_eq_finrank_intH1` (sorry, UCT + free-ℤ-module
  algebra); `realDim_deRhamH1_eq_finrank_intH1` (sorry-free assembly).

- `Jacobian/Periods/IntegralOneCycleRank.lean` — pure-algebra leaves:
  `IntegralOneCycle_finite` (sorry), `IntegralOneCycle_torsionFree`
  (sorry), `finrank_homℤℝ_eq_finrank_of_free` (sorry, ARISTOTLE-SIZED
  pure algebra ~40 lines).

- `Jacobian/HolomorphicForms/HodgeDeRhamRank.lean` — outer assembly:
  `two_analyticGenus_eq_finrank_intH1` (sorry-free assembly of the Hodge
  side and de Rham side).

### Refinement chain

```text
hodge_deRham_rank_eq                                -- PeriodFunctional.lean (✅ sorry-free)
└── two_analyticGenus_eq_finrank_intH1              -- HodgeDeRhamRank.lean (✅ sorry-free)
    ├── realDimDeRhamH1_eq_two_analyticGenus        -- HodgeDecomposition.lean (✅ sorry-free)
    │   ├── realDim_deRhamH1_eq_complexDim_deRhamH1ℂ  -- DeRhamCohomology.lean (sorry)
    │   ├── complexDimDeRhamH1ℂ_eq_analyticHarmonicGenus
    │   │                                              -- HodgeDecomposition.lean (sorry)
    │   ├── analyticHarmonicGenus_eq_analyticGenus_add_anti
    │   │                                              -- HodgeStarRS.lean (sorry)
    │   └── analyticAntiGenus_eq_analyticGenus       -- AntiHolomorphicOneForm.lean (rfl-via-alias)
    └── realDim_deRhamH1_eq_finrank_intH1            -- DeRhamSingular.lean (✅ sorry-free)
        ├── realDim_deRhamH1_eq_realDim_singularH1    -- DeRhamSingular.lean (sorry, de Rham theorem)
        └── realDim_singularH1_eq_finrank_intH1       -- DeRhamSingular.lean (sorry)
            └── factors through IntegralOneCycle_finite,
                IntegralOneCycle_torsionFree,
                finrank_homℤℝ_eq_finrank_of_free      -- IntegralOneCycleRank.lean (3 sorries)
```

### Sorry inventory (frontier obligations, after refinement)

| File | Decl | Class |
| --- | --- | --- |
| `DeRhamCohomology.lean` | `realDim_deRhamH1_eq_complexDim_deRhamH1ℂ` | major analytic |
| `DeRhamCohomology.lean` | `complexDim_deRhamH0ℂ_eq_one_of_compact_connected` | analytic (downstream) |
| `DeRhamCohomology.lean` | `realDim_deRhamH0_eq_one_of_compact_connected` | analytic (downstream) |
| `HodgeStarRS.lean` | `analyticHarmonicGenus_eq_analyticGenus_add_anti` | major analytic (Hodge ⋆) |
| `HodgeStarRS.lean` | `analyticHarmonicGenus_finite` | analytic (elliptic regularity) |
| `HodgeDecomposition.lean` | `complexDimDeRhamH1ℂ_eq_analyticHarmonicGenus` | major analytic (Hodge theorem) |
| `DeRhamSingular.lean` | `realDim_deRhamH1_eq_realDim_singularH1` | **major analytic** (de Rham theorem) |
| `DeRhamSingular.lean` | `realDim_singularH1_eq_finrank_intH1` | algebra (factors through algebra leaves) |
| `IntegralOneCycleRank.lean` | `IntegralOneCycle_finite` | **major topology** (cellular homology) |
| `IntegralOneCycleRank.lean` | `IntegralOneCycle_torsionFree` | topology (UCT + Poincaré) |
| `IntegralOneCycleRank.lean` | `finrank_homℤℝ_eq_finrank_of_free` | **pure algebra (Aristotle-sized)** |
| `AntiHolomorphicOneForm.lean` | `module_finite_of_compact` | inheritable (alias) |

The single original `sorry` in `hodge_deRham_rank_eq` has been replaced
by a tree of ~12 named frontier obligations, each precisely scoped.
The pure-algebra leaf `finrank_homℤℝ_eq_finrank_of_free` is
Aristotle-sized; the major analytic leaves remain multi-month Mathlib
efforts as flagged by the blueprint's red-border umbrella status.

### Round 2 deeper refinement

A second TOPDOWN pass refined seven of the round-1 frontier sorries
into substantively smaller named ingredients across **six new
modules**:

- `Jacobian/HolomorphicForms/SmoothDifferentialForm.lean` — opaque
  `SmoothDiffForm n X` (currently aliased to `Fin n.succ →
  HolomorphicOneForm ℂ X`), opaque `exteriorDerivative n X`,
  named `exteriorDerivative_squared_eq_zero`,
  `ExactForm_le_ClosedForm`, plus `ClosedFormSub` instance hooks.

- `Jacobian/HolomorphicForms/DeRhamComplex.lean` — concrete model
  `deRhamH1Cocycle X := ClosedForm 1 X ⧸ ExactForm.toClosedSubmodule 0 X`
  with explicit AddCommGroup/Module instances; named identities
  `complexDimDeRhamH1ℂ_eq_finrank_cocycle` and
  `realDimDeRhamH1_eq_finrank_cocycleℝ`.

- `Jacobian/HolomorphicForms/DeRhamComparisonMap.lean` —
  decomposes the **de Rham theorem** sorry into:
  - `deRhamComparisonMap1` (opaque integration map),
  - `deRhamComparisonMap1_vanishes_on_exact` (sorry, **STOKES**),
  - `deRhamComparisonMap1_surjective` (sorry, prescribed-period),
  - `deRhamComparisonMap1_kernel_subset_exact` (sorry, vanishing periods ⇒ exact),
  - `deRhamComparisonMap1_descends`, `deRhamH1Cocycle_finrank_eq_realDim_singularH1`,
  - `realDimDeRhamH1_eq_realDimSingularH1_via_cocycle` (sorry-free assembly).
  Now `realDim_deRhamH1_eq_realDim_singularH1` (in `DeRhamSingular.lean`)
  delegates to this via_cocycle assembly, making three sub-leaves
  named replacements for the original monolithic sorry.

- `Jacobian/HolomorphicForms/RealSingularH1.lean` — moved the
  `realDimSingularH1` opaque to a tiny standalone module to break the
  potential import cycle.

- `Jacobian/HolomorphicForms/HodgeLaplacian.lean` — opaque
  `hodgeStarOp`, `dStarOperator1`, `dStarOperator2`, `hodgeLaplacian1`;
  named identities `hodgeStarOp_squared`, `hodgeLaplacian1_def`,
  `hodgeLaplacian1_kernel_iff`, `harmonicEquivLaplacianKernel`,
  `hodgeLaplacian1_kernel_finite` (each a precise frontier sorry).

- `Jacobian/HolomorphicForms/HodgeProjection.lean` — decomposes the
  **Hodge harmonic projection** sorry into:
  - `harmonicProjection1` (opaque),
  - `harmonicProjection1_surjective` (sorry),
  - `harmonicProjection1_vanishes_on_exact` (sorry, **HODGE ORTHOGONALITY**),
  - `harmonicProjection1_kernel_eq_exact` (sorry),
  - `deRhamH1_isLinearEquiv_harmonic` (sorry, **HODGE THEOREM**),
  - `complexDimDeRhamH1ℂ_eq_analyticHarmonicGenus_via_cocycle` (sorry-free assembly).
  Now `complexDimDeRhamH1ℂ_eq_analyticHarmonicGenus` (in
  `HodgeDecomposition.lean`) delegates to this via_cocycle assembly.

- `Jacobian/Periods/CellularHomologyRS.lean` — decomposes the
  **cellular homology** sorries into:
  - `FiniteCWStructure X` (opaque),
  - `compactRiemannSurface_hasFiniteCWStructure` (sorry, **RADÓ**),
  - `numCells X cw n`, `CellularChainModule` (alias `Fin _ →₀ ℤ`,
    sorry-free `Free`/`Finite` instances),
  - `IntegralOneCycle_isomorphic_cellularH1` (sorry,
    cellular ↔ singular comparison),
  - `IntegralOneCycle_finite_via_cellular`,
  - `IntegralOneCycle_torsionFree_via_cellular` (sorry-free assemblies).
  Now `IntegralOneCycle_finite` and `IntegralOneCycle_torsionFree`
  in `IntegralOneCycleRank.lean` delegate to these via_cellular
  assemblies.

- `Jacobian/Periods/RealHomologyTensor.lean` — decomposes the
  **UCT** sorry into:
  - `realDimSingularH1_eq_finrank_intHom1` (sorry, UCT half),
  - `realDim_singularH1_eq_finrank_intH1_via_uct` (sorry-free assembly).
  Now `realDim_singularH1_eq_finrank_intH1` (in `DeRhamSingular.lean`)
  delegates to this via_uct assembly.

- `Jacobian/Periods/FreeModuleHomFinrank.lean` — decomposes the
  **pure-algebra** sorry into:
  - `homℤℝ_basis_evaluation_isLinearEquivℝ` (sorry, ARISTOTLE-SIZED
    basis-evaluation iso),
  - `finrank_pi_real_eq_card` (sorry, small Mathlib lookup),
  - `finrank_homℤℝ_eq_basis_card` (sorry-free assembly),
  - `finrank_homℤℝ_eq_finrank_of_free_via_basis` (frontier with
    one residual basis-finiteness sorry).
  Now `finrank_homℤℝ_eq_finrank_of_free` (in `IntegralOneCycleRank.lean`)
  delegates to this via_basis assembly.

- `Jacobian/HolomorphicForms/RealComplexDeRham.lean` — decomposes
  the **real-of-complex** identity into:
  - `complexDeRhamH1_eq_tensorℂ_realDeRhamH1` (sorry, EXTENSION OF SCALARS),
  - `tensorℂ_finrank_eq_real_finrank` (sorry, ARISTOTLE-SIZED algebra),
  - `realDim_deRhamH1_eq_complexDim_deRhamH1ℂ` (sorry-free assembly,
    moved from `DeRhamCohomology.lean`).

### Round-2 sorry inventory (frontier obligations)

After round 2, the named frontier obligations directly reachable
from `hodge_deRham_rank_eq` include:

| File | Decl | Class |
| --- | --- | --- |
| `SmoothDifferentialForm.lean` | `exteriorDerivative_squared_eq_zero` | analytic (chain rule + antisymmetry) |
| `SmoothDifferentialForm.lean` | `ExactForm_le_ClosedForm` | algebra (ARISTOTLE-SIZED) |
| `DeRhamComplex.lean` | `complexDimDeRhamH1ℂ_eq_finrank_cocycle` | bridge (defining identity) |
| `DeRhamComplex.lean` | `realDimDeRhamH1_eq_finrank_cocycleℝ` | bridge |
| `DeRhamComparisonMap.lean` | `deRhamComparisonMap1_vanishes_on_exact` | **STOKES** (major) |
| `DeRhamComparisonMap.lean` | `deRhamComparisonMap1_surjective` | major analytic (period prescription) |
| `DeRhamComparisonMap.lean` | `deRhamComparisonMap1_kernel_subset_exact` | major analytic (Poincaré + sheaves) |
| `DeRhamComparisonMap.lean` | `deRhamComparisonMap1_descends` | small (corollary) |
| `DeRhamComparisonMap.lean` | `deRhamH1Cocycle_finrank_eq_realDim_singularH1` | bridge |
| `HodgeLaplacian.lean` | `hodgeStarOp_squared` | analytic (Riemann-surface ⋆ identity) |
| `HodgeLaplacian.lean` | `hodgeLaplacian1_def` | analytic (definition) |
| `HodgeLaplacian.lean` | `hodgeLaplacian1_kernel_iff` | analytic (integration by parts) |
| `HodgeLaplacian.lean` | `harmonicEquivLaplacianKernel` | analytic (`Harm¹ = ker Δ`) |
| `HodgeLaplacian.lean` | `hodgeLaplacian1_kernel_finite` | major analytic (ELLIPTIC REGULARITY) |
| `HodgeProjection.lean` | `harmonicProjection1_surjective` | major analytic |
| `HodgeProjection.lean` | `harmonicProjection1_vanishes_on_exact` | major analytic (HODGE ORTHOGONALITY) |
| `HodgeProjection.lean` | `harmonicProjection1_kernel_eq_exact` | major analytic |
| `HodgeProjection.lean` | `deRhamH1_isLinearEquiv_harmonic` | **HODGE THEOREM** |
| `CellularHomologyRS.lean` | `compactRiemannSurface_hasFiniteCWStructure` | **RADÓ** (red-border umbrella) |
| `CellularHomologyRS.lean` | `IntegralOneCycle_isomorphic_cellularH1` | major topology |
| `RealHomologyTensor.lean` | `realDimSingularH1_eq_finrank_intHom1` | major topology (UCT) |
| `RealComplexDeRham.lean` | `complexDeRhamH1_eq_tensorℂ_realDeRhamH1` | analytic (extension of scalars) |
| `RealComplexDeRham.lean` | `tensorℂ_finrank_eq_real_finrank` | algebra (ARISTOTLE-SIZED) |
| `FreeModuleHomFinrank.lean` | `homℤℝ_basis_evaluation_isLinearEquivℝ` | algebra (ARISTOTLE-SIZED ~30 lines) |
| `FreeModuleHomFinrank.lean` | `finrank_pi_real_eq_card` | small Mathlib lookup |
| `FreeModuleHomFinrank.lean` | `finrank_homℤℝ_eq_finrank_of_free_via_basis` | algebra (residual basis finiteness) |
| `DeRhamCohomology.lean` | `complexDim_deRhamH0ℂ_eq_one_of_compact_connected` | analytic (downstream) |
| `DeRhamCohomology.lean` | `realDim_deRhamH0_eq_one_of_compact_connected` | analytic (downstream) |
| `HodgeStarRS.lean` | `analyticHarmonicGenus_eq_analyticGenus_add_anti` | major analytic (Hodge ⋆ split) |
| `HodgeStarRS.lean` | `analyticHarmonicGenus_finite` | analytic (elliptic regularity) |

That's **30 named frontier obligations**, each precisely scoped to
a single mathematical statement, replacing the original monolithic
`sorry` in `hodge_deRham_rank_eq`.  Several Aristotle-sized leaves
(pure algebra, basis arguments, simple Mathlib lookups) are now
extracted, and the major classical inputs (Stokes, Hodge,
Radó, UCT) are separately named for tracking against the
red-border umbrellas in the blueprint.

## Practical Guardrails

- Keep `Solution.lean` independent of `Challenge.lean`.
- Keep public declaration names and statement shapes identical to the challenge.
- Prefer importing production umbrellas into `Solution.lean` only when the
  imported declarations are stable enough to be part of the comparison story.
- Avoid broad new opaque declarations. If an opaque or `sorry` is unavoidable,
  give it a mathematically precise name and place it in the layer that should
  eventually prove it.
- Record every new helper obligation in this file or `aristotle_tasks.md`.
- Comparator is a check, not the design driver. The mathematical spine above is
  the design driver.
