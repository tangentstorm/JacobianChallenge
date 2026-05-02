# Plan: `thm:polygonal-model`

Blueprint label: `thm:polygonal-model`
Lean handle: `JacobianChallenge.Blueprint.polygonal_model`
File: `Jacobian/Blueprint/Sec03/PolygonalModel.lean`
Class: **DECOMPOSE** (currently real signature, body = `sorry`)

## 1. Mathematical statement

```
theorem polygonal_model
    (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (g : ℕ) (_hg : analyticGenus ℂ X = g) :
    Nonempty (X ≃ₜ Polygon4g g)
```

A compact connected oriented Riemann surface of analytic genus `g` is
homeomorphic to the standard fundamental polygon `Polygon4g g`
(constructed in `Jacobian/Periods/Polygon4g.lean` as a quotient of the
closed unit disk by the standard `4g`-gon side-pairing).

## 2. Structural split (Grok-seeded)

Grok's external outline (preserved at
`ref/brainstorm/polygonal_model-grok-outline.lean`) suggests a clean
3-stage decomposition:

**Stage A — Topology.** Every compact connected oriented topological
2-manifold `M` is homeomorphic to `Polygon4g g'` for a unique `g' : ℕ`
(the topological genus). This is the *surface classification theorem*.

**Stage B — Bridge.** For a compact connected Riemann surface `X`, the
analytic genus `analyticGenus ℂ X` (defined via
`FiniteDimensionalHolomorphicOneForms`) coincides with the topological
genus of the underlying 2-manifold.

**Stage C — Complex-to-real conversion + assembly.** A Riemann surface
is automatically a smooth oriented 2-manifold; combine A + B to derive
the homeomorphism with the right `Polygon4g g`.

Splitting the proof this way decouples the heavy classical-topology
work (Stage A) from the complex-analytic content (Stage B). Stage C is
a few lines of glue.

## 3. Mathlib v4.28.0 inventory

| prerequisite | status | path |
|---|---|---|
| `Polygon4g g` (project) | PRESENT | `Jacobian/Periods/Polygon4g.lean` (164 LOC, sorry-free) |
| `analyticGenus ℂ X` (project) | PRESENT | `Jacobian/HolomorphicForms/AnalyticGenus.lean` |
| `FiniteDimensionalHolomorphicOneForms` typeclass | PRESENT | `Jacobian/HolomorphicForms/FiniteDimensional.lean` |
| Smooth-2-manifold-from-complex-1-manifold conversion | PARTIAL | Mathlib has `IsManifold (modelWithCornersSelf ℂ ℂ)` and `IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))`; conversion may need a project wrapper |
| Orientability of complex manifolds | ABSENT (no `Orientable` typeclass yet) | — |
| Surface classification (Stage A) | ABSENT | — (the big gap; see `ref/plans/surface-classification.md` if/when written) |
| Analytic-vs-topological genus equivalence (Stage B) | ABSENT | — (Hodge theory or de Rham + Riemann-Roch route) |
| Triangulation of compact 2-manifolds (Radó for Riemann surfaces) | ABSENT | — |
| Singular homology `H_1(X, ℤ)` | PRESENT | `Mathlib.AlgebraicTopology.SingularHomology` |

## 4. Decomposition (3 + sub-stages)

### Stage A — Surface classification (the big one)

Sub-leaves (each is itself a multi-hundred-LOC project; this would
warrant its own dedicated plan `ref/plans/surface-classification.md`):

| # | Lean handle | Class | Sketch |
|---|---|---|---|
| A1 | `compact_2manifold_admits_triangulation` | HARD | Radó-style: every compact 2-manifold admits a finite triangulation. |
| A2 | `triangulated_orientable_surface_word` | HARD | Combinatorial reduction: any triangulated compact orientable 2-manifold's edge-pairing word reduces to the standard `a₁b₁a₁⁻¹b₁⁻¹⋯` after finite Tietze-style moves. |
| A3 | `polygon_word_to_quotient` | MEDIUM | The standard word identifies precisely with our `Polygon4g g`. |
| A4 | `compact_orientable_surface_classification` (umbrella) | SHORT | Assemble A1 + A2 + A3 into `Nonempty (M ≃ₜ Polygon4g g')`. |

Estimated LOC: ~3000–5000. **This is the actual blocker.** Decomposing
A1 and A2 into Aristotle-reachable leaves is the next-level planning
task.

### Stage B — Analytic ↔ topological genus

| # | Lean handle | Class | Sketch | Mathlib ready? |
|---|---|---|---|---|
| B1 | `complex_manifold_to_smooth_real` | MEDIUM | A complex 1-manifold structure on `X` induces a smooth 2-manifold structure (via `ChartedSpace ℂ X` + a fixed `ℂ ≃ₗ[ℝ] ℝ²` to get charts into `EuclideanSpace ℝ (Fin 2)`). | partial — Mathlib has `Complex.equivRealProd` |
| B2 | `complex_manifold_orientable` | MEDIUM | Holomorphic transition maps have positive Jacobian, so the induced smooth structure is orientable. Requires an `Orientable` typeclass (would have to define at the project level since Mathlib lacks it). | needs project work |
| B3 | `topologicalGenus` definition | MEDIUM | Define `topologicalGenus M = (rank H_1(M, ℤ)) / 2` for a compact orientable 2-manifold (well-defined by Stage A). | uses Mathlib's `SingularHomology` |
| B4 | `analyticGenus_eq_topologicalGenus` | HARD | The identity `analyticGenus ℂ X = topologicalGenus X` for compact connected Riemann surfaces. Classical proofs: Hodge theory, de Rham + Riemann-Roch, or Stokes-on-RS bookkeeping. | needs Hodge theory or a substantial chunk of de Rham/RR |
| B5 | `analyticGenus_topologicalGenus_bridge` (umbrella) | SHORT | Combine B1–B4. | trivial assembly |

Estimated LOC: ~2000–4000. **Stage B is independent of Stage A and can
proceed in parallel.** B4 is the hardest leaf; the others are
infrastructure.

### Stage C — Assembly

| # | Lean handle | Class | Sketch |
|---|---|---|---|
| C1 | `polygonal_model` | SHORT | Apply B1–B2 to get a smooth oriented 2-manifold structure on `X`. Apply Stage A to get `Nonempty (X ≃ₜ Polygon4g g')` for some `g'`. By `_hg` and B4, `g = g'`. Return the homeomorphism. |

LOC: ~30.

## 5. Assembly order

1. Build out `Jacobian/Periods/Polygon4g.lean` (DONE).
2. Stage B1, B2, B3 (definitional + relatively cheap).
3. Stage A1, A2 (the surface-classification gap — the big project).
4. Stage A3, A4 (small assembly above A1+A2).
5. Stage B4 (the analytic-vs-topological genus identity).
6. Stage B5 (umbrella).
7. Stage C1 (final assembly).

## 6. What is genuinely blocked

**Stage A1 (Radó's triangulation theorem)** is the single largest
classical-topology gap. Without it, surface classification cannot
proceed in Lean at all. Once A1 is proved (or axiomatized at the
project level pending a Mathlib PR), A2–A4 become essentially
combinatorial.

**Stage B4 (genus equivalence)** is the second-largest gap. The
Hodge-theoretic route requires `H^{0,1}` Dolbeault cohomology on
Riemann surfaces, which Mathlib lacks. The de Rham + Riemann-Roch
route requires Stokes-on-RS-with-boundary (already planned
`ref/plans/stokes-on-rs-with-boundary.md`) plus Riemann-Roch
(already planned via `input:riemann-roch`).

**`Orientable` typeclass** — Mathlib v4.28.0 doesn't have one. Either
(a) wait for it to land in Mathlib, or (b) define a project-side
`Orientable` predicate on compact smooth manifolds.

## 7. LOC estimate (top-line)

| Stage | LOC range |
|---|---|
| A (surface classification) | 3000–5000 |
| B (genus equivalence + scaffolding) | 2000–4000 |
| C (assembly) | ~30 |
| **Total** | **5000–9000 LOC** |

This is the largest single project in the JacobianChallenge program
(comparable to existing differential-geometry or algebraic-topology
chunks of Mathlib). It is genuinely worth its own multi-month
sub-project — and it is the cleanest path to a no-axiom Jacobian
challenge.

## 8. Recommendations

1. **Begin with Stage B's scaffolding (B1–B3)** since it's cheaper and
   independent of Stage A. Each piece is achievable today against
   Mathlib v4.28.0.
2. **Park Stage A as a separate planning effort.** Open
   `ref/plans/surface-classification.md` and route through a focused
   Grok+ChatGPT planning round on Radó vs. handle-decomposition vs.
   Morse-theory routes. The right route for Lean is non-obvious.
3. **Stage C is one-line glue** — write it the moment A and B land.

For now `Jacobian/Blueprint/Sec03/PolygonalModel.lean` retains its
sorry-bound umbrella with the real type signature; that's already
the right scaffold.

## 9. Top-down refinement progress (2026-05)

`Jacobian/Blueprint/Sec03/PolygonalModel.lean` no longer carries a
single monolithic `sorry`. The body of `polygonal_model` is now an
*assembly* delegating to four named obligations:

* `JacobianChallenge.Periods.ChartedSpaceComplex_to_smoothReal2`
  (Stage B1, real proof — preexisting in
  `Jacobian/Periods/SmoothRealStructure.lean`).
* `JacobianChallenge.Periods.complexManifold_orientable`
  (Stage B2, instance — new
  `Jacobian/Periods/ComplexManifoldOrientable.lean`; placeholder
  witness from the `True`-field `Orientable` class).
* `JacobianChallenge.Periods.compactOrientableSurface_homeomorph_polygon4g_topologicalGenus`
  (Stage A umbrella — new
  `Jacobian/Periods/SurfaceClassification.lean`, *no own `sorry`*).
* `JacobianChallenge.Periods.analyticGenus_eq_topologicalGenus`
  (Stage B umbrella — new
  `Jacobian/Periods/AnalyticGenusEqTopologicalGenus.lean`,
  *no own `sorry`*).

### Stage A refinement (`SurfaceClassification.lean`)

The Stage A umbrella body assembles three further leaves:

* `existsPolygonalQuotientPresentation` (Stage A1+A2, **named sorry**)
  — for compact connected orientable smooth real 2-manifold `M`,
  exists `g'` and a continuous surjection `q : DiskC → M` whose fibres
  coincide with `Polygon4g.SideRel g'`. This is the heart of the
  classical surface-classification theorem (Radó + combinatorial
  reduction to the standard `4g'`-gon edge word). Discharge would
  itself require a multi-thousand-LOC sub-project; recommend opening
  `ref/plans/surface-classification.md` for the next-level decomposition.
* `polygonalQuotientPresentation_to_homeo` (Stage A3+A4, **real proof**)
  — universal-property assembly: lifts `q` through the side-pairing
  quotient via `Quotient.lift`, derives bijectivity from the kernel
  iff, upgrades to a homeomorphism via
  `Continuous.homeoOfEquivCompactToT2`.
* `existsHomeoToPolygon4g` (**real proof, derived**) — combines the
  two above.

The Stage A umbrella additionally uses:

* `singularH1_polygon4g_finrank` (**named sorry**) — the polygon's
  singular `H₁` has ℤ-rank `2g`. Bottom-up: cellular homology on the
  one-vertex `2g`-edge one-2-cell CW structure with attaching word
  `∏ [aᵢ,bᵢ]`.
* `topologicalGenus_polygon4g` (**real proof**) — Nat division wrap
  around the leaf above.
* `topologicalGenus_homeo_invariant` (**real proof**) — unfolds and
  rewrites through `singularH1_finrank_homeo_invariant` (now in
  `Jacobian/Periods/TopologicalGenusInvariance.lean`, *no sorry*)
  via `TopCat.isoOfHomeo` + functoriality of
  `singularHomologyFunctor (ModuleCat ℤ) 1` + `Iso.toLinearEquiv` +
  `LinearEquiv.finrank_eq`.

### Stage B refinement (`AnalyticGenusEqTopologicalGenus.lean`)

The Stage B umbrella body delegates to a single ℤ-rank leaf:

* `singularH1_finrank_eq_two_mul_analyticGenus` (**named sorry**)
  — `Module.finrank ℤ (singularH1 X) = 2 * analyticGenus ℂ X` for
  compact connected Riemann surfaces.

Meet-in-the-middle: this is the same statement as the project's
existing `JacobianChallenge.Periods.hodge_deRham_rank_eq` in
`Jacobian/Periods/PeriodFunctional.lean`, modulo the
`IntegralOneCycle X = singularH1 X` definitional identification and
the duplicate `topologicalGenus` definitions (one in `TopologicalGenus`,
one in `PeriodFunctional`). When those are unified, this leaf
discharges directly.

### Current named-sorry frontier (3 leaves)

| Leaf | File | Bottom-up content |
| --- | --- | --- |
| `existsPolygonalQuotientPresentation` | `SurfaceClassification.lean` | Surface classification (Radó + edge-word reduction) |
| `singularH1_polygon4g_finrank` | `SurfaceClassification.lean` | Cellular `H₁` of the standard `4g`-gon CW structure |
| `singularH1_finrank_eq_two_mul_analyticGenus` | `AnalyticGenusEqTopologicalGenus.lean` | Hodge / de Rham + Riemann-Roch / period-lattice |

### Build status

`lake build Jacobian.Blueprint.Sec03.PolygonalModel` succeeds. The
`polygonal_model` declaration has no own `sorry`; the only remaining
`sorry`s in its dependency closure are the three leaves above
(plus pre-existing project sorries unchanged by this refinement).
