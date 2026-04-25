# Phase 0.5 Mathlib Inventory

Audit of the pinned Mathlib commit for infrastructure needed by the Jacobian
Challenge. Produced against:

- Lean: `leanprover/lean4:v4.28.0`
- Mathlib: `lake-manifest.json` pins `v4.28.0` at
  `8f9d9cff6bd728b17a24e163c9402775d9e6a365`
- Note: `Jacobian/Challenge.lean` comments reference
  `8e3c989104daaa052921bf43de9eef0e1ac9fbf5` (15 Apr 2026). The source on disk
  is the v4.28.0 tag; the delta should be checked, but is not expected to
  substantively change this inventory.

All paths below are rooted at `.lake/packages/mathlib/Mathlib/`.

Legend: **PRESENT** = usable as-is. **PARTIAL** = pieces exist but a gap must
be bridged. **ABSENT** = needs to be built from scratch.

---

## 1. Bridge to the Challenge File API

Everything that appears textually in `Jacobian/Challenge.lean`.

### 1.1 `IsManifold` and `ω` smoothness — **PRESENT**

- `IsManifold` — `Geometry/Manifold/IsManifold/Basic.lean:783`.
  Class over `(I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞) (M : ...)`,
  extends `HasGroupoid M (contDiffGroupoid n I)`.
- `ω` notation — `Analysis/Calculus/ContDiff/FTaylorSeries.lean:112`:
  `scoped[ContDiff] notation3 "ω" => (⊤ : WithTop ℕ∞)`.
- On complex models (`𝓘(ℂ)` / `𝓘(ℂ, E)`), `ContMDiff … ω` is the definition
  of holomorphic; there is no separate `Holomorphic` predicate.

### 1.2 `ContMDiff` API — **PRESENT**

- Definitions — `Geometry/Manifold/ContMDiff/Defs.lean:164–192`.
- Composition, identity, locality lemmas — `Geometry/Manifold/ContMDiff/Basic.lean`.

### 1.3 `LieAddGroup` and `→ₜ+` — **PRESENT**

- `LieAddGroup` — `Geometry/Manifold/Algebra/LieGroup.lean:61`, extends
  `ContMDiffAdd I n G` and adds `contMDiff_neg`.
- `→ₜ+` infix — `Topology/Algebra/ContinuousMonoidHom.lean:74`
  (`ContinuousAddMonoidHom`, extends `A →+ B` and `C(A, B)`).

### 1.4 `modelWithCornersSelf` and `𝓘(ℂ)` — **PRESENT**

- Definition — `Geometry/Manifold/IsManifold/Basic.lean:211`.
- Notations `𝓘(𝕜)` and `𝓘(𝕜, E)` — lines 215–218.

### 1.5 Models with all instances the challenge needs — **PRESENT**

- `ℂ`, `EuclideanSpace ℝ (Fin n)`, `Fin n → ℂ`, products: full `ChartedSpace`
  and `IsManifold` infrastructure.
- Product charted space — `Geometry/Manifold/ChartedSpace.lean:432`.

### 1.6 Sphere — **PARTIAL (critical gap)**

- `EuclideanSpace.instChartedSpaceSphere` — `Geometry/Manifold/Instances/Sphere.lean:352`.
- `EuclideanSpace.instIsManifoldSphere` — line 386, as a **real** analytic
  manifold (`𝓡 n` model).
- `Circle` as `LieGroup (𝓡 1) ω Circle` — Sphere.lean:549–556.

**Gap:** `Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1` has **no**
`IsManifold 𝓘(ℂ) ω` instance. The challenge statement `genus_eq_zero_iff_homeo`
only asks for homeomorphism to the sphere (a topological statement), so this
gap does not block stating the lemma — but it does mean the sphere cannot be
compared to `X` as complex manifolds when we prove the lemma.

### 1.7 Riemann surface / genus / divisor / RR — **ABSENT**

- No `RiemannSurface`, `genus`, `MeromorphicFunction`, `Divisor` (in the
  geometric sense), `RiemannRoch`.

---

## 2. Quotients, Lattices, Complex Tori (Phase 1 support)

### 2.1 `Z`-lattices — **PRESENT**

- `IsZLattice K L` — `Algebra/Module/ZLattice/Basic.lean:433`.
- `ZSpan.fundamentalDomain`, `ZSpan.quotientEquiv` — lines 92 and 270.
- `ZLattice.module_free`, `ZLattice.rank`, `ZLattice.basis` — lines 510, 523, 684.
- `DiscreteTopology (span ℤ (Set.range b))` for `[Finite ι]` — line 318.
- Fundamental domain is measurable; quotient is a compact fundamental domain.

### 2.2 Topological quotient by subgroup — **PARTIAL**

- `QuotientGroup.instTopologicalSpace` — `Topology/Algebra/Group/Quotient.lean:32`.
- `QuotientGroup.instT1Space` (for closed subgroups) — line 105.
- `QuotientGroup.instCompactSpace` — line 36.
- `QuotientGroup.instLocallyCompactSpace` — line 117.
- `QuotientAddGroup.instT3Space` (via `to_additive`).

**Gap:** T2/Hausdorff specifically for `ℂⁿ ⧸ Λ` with a closed discrete `Λ`
follows from `T3 ⇒ T2`, but the project will want a direct lemma.

### 2.3 Quotient manifold by a discrete group action — **ABSENT**

- No `ChartedSpace.quotient`, no `Quotient.chartedSpace`, no
  `MulAction.QuotientChartedSpace` anywhere in `Geometry/Manifold/`.
- Zulip April 2026: Michael Rothgang said "the charted space instance is
  awaiting review"; it has **not** landed at v4.28.0.

### 2.4 `LieAddGroup` / smooth-manifold instance on `V ⧸ Λ` — **ABSENT**

- No combined instance. Must be assembled: fundamental-domain chart
  construction + transition maps + verification that addition/negation
  descend smoothly.

**First-milestone summary.** `plan.md` picks, as its first concrete
milestone, a standalone file proving that a finite-dimensional complex vector
space modulo a full lattice is a compact complex Lie additive group. The
inventory says: the lattice side is ready (§2.1); the quotient-topology side
is mostly ready (§2.2); the manifold side is the thing we have to build
(§2.3, §2.4).

---

## 3. Differential Forms (Phase 2 support)

### 3.1 Exterior derivative on normed spaces — **PRESENT**

- `extDeriv`, `extDerivWithin` — `Analysis/Calculus/DifferentialForm/Basic.lean:73–90`.
- `d² = 0`: `extDerivWithin_extDerivWithin_apply` (line 204) and
  `extDeriv_extDeriv` (line 235).
- Only on normed spaces `E`; not lifted to manifold sections.

### 3.2 Alternating / multilinear — **PRESENT**

- `AlternatingMap` — `LinearAlgebra/Alternating/Basic.lean:68`.
- `ContinuousAlternatingMap` (notation `E [⋀^Fin n]→L[𝕜] F`) — used
  throughout `Analysis/Calculus/DifferentialForm/Basic.lean:20`.
- `ExteriorAlgebra` — `LinearAlgebra/ExteriorAlgebra/Basic.lean`.

### 3.3 Tangent bundle and smooth sections — **PRESENT**

- `TangentBundle I M` as a vector bundle —
  `Geometry/Manifold/VectorBundle/Tangent.lean:85`.
- `ContMDiffSection` with addition/scalar-multiplication —
  `Geometry/Manifold/VectorBundle/SmoothSection.lean:17`.
- Module structure on sections; **no** finite-dimensionality of global
  sections on a compact manifold.

### 3.4 Differential forms on manifolds — **ABSENT**

- No `MDifferentialForm`, `SmoothOneForm`, `HolomorphicOneForm`.
- No manifold-level `extDeriv`.
- **Bootstrap route**: define 1-forms as `ContMDiffSection` of the dual
  tangent bundle, chart-locally push through `extDeriv` on the model, glue via
  transition functions. Infrastructure to host this exists; the type itself
  does not.
- `Geometry/Manifold/Complex.lean:26–37` has a TODO explicitly listing
  "finite-dimensionality of holomorphic sections" and "sheaves of holomorphic
  / meromorphic functions" as future work.

### 3.5 Finite-dimensionality `dim H⁰(X, Ω¹) = g` — **ABSENT**

- Not stated anywhere. Requires Riemann–Roch / Hodge / Serre-duality-type
  input.

---

## 4. Integration, Paths, Homology (Phase 3 support — **the bottleneck**)

### 4.1 Path / curve integration in normed spaces — **PRESENT**

- `curveIntegral` (`∫ᶜ x in γ, ω x`) — `MeasureTheory/Integral/CurveIntegral/Basic.lean:103`.
  Takes `ω : E → E →L[𝕜] F` and `γ : Path a b` in a normed space `E`.
- `CurveIntegrable`, `curveIntegral_add`, `curveIntegral_trans`,
  `curveIntegral_symm`, `curveIntegral_refl` — same file.
- `Poincaré` lemma for convex subsets —
  `MeasureTheory/Integral/CurveIntegral/Poincare.lean:16`.
- Complex contour / Cauchy — `Analysis/Complex/CauchyIntegral.lean`:
  `Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable`,
  `Complex.integral_boundary_rect_of_hasFDerivAt_real_off_countable`.
- `Analysis/BoxIntegral/DivergenceTheorem.lean` and
  `MeasureTheory/Integral/DivergenceTheorem.lean` give Stokes on boxes.

### 4.2 Path / curve integration on manifolds — **ABSENT**

- `Path a b` requires `a b : E` for a normed space. No path integral type
  takes `γ : C([0,1], M)` on a manifold.
- No bridge from `curveIntegral` through a chart atlas.

### 4.3 Singular homology — **PARTIAL**

- `singularChainComplexFunctor`, `singularHomologyFunctor` —
  `AlgebraicTopology/SingularHomology/Basic.lean` (added 2025).
- Only concrete computation: `singularHomologyFunctorZeroOfTotallyDisconnectedSpace`.
- Homological algebra backbone (chain complexes, homology functors, short
  exact sequences) — `Algebra/Homology/` — mature.

**Gaps:** no cap product, no Künneth, no fundamental class for oriented
manifolds, no computation of `H₁` for a compact surface, no pairing with
differential forms.

### 4.4 Fundamental group / π₁ ↔ H₁ — **PARTIAL**

- `FundamentalGroup`, `FundamentalGroupoid`, `Path` homotopy quotient —
  `AlgebraicTopology/FundamentalGroupoid/FundamentalGroup.lean:35`.
- `Path` algebra, path-homotopy equivalence — `Topology/Path.lean`,
  `Topology/Homotopy/Path.lean`.
- `PathConnectedSpace`, `PathComponent` — `Topology/Connected/PathConnected.lean`.

**Gap:** no Hurewicz homomorphism `π₁^{ab} → H₁(X, ℤ)`; no abelianization
comparison. We cannot cheaply substitute `π₁^{ab}` for `H₁` without building
this.

### 4.5 Stokes / de Rham on manifolds — **ABSENT**

- Only box / rectangle versions; nothing on manifolds with boundary; no
  de Rham cohomology.

**This is the single largest gap for the period-lattice route.**

---

## 5. Local Theory of Holomorphic Maps (Phase 6 support)

### 5.1 Power-series / local normal form — **PRESENT**

- `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff` —
  `Analysis/Analytic/IsolatedZeros.lean:190`.
- `HasFPowerSeriesAt.eq_pow_order_mul_iterate_dslope` — IsolatedZeros.lean:102.
- `FormalMultilinearSeries.order` — `Analysis/Analytic/Order.lean`.

### 5.2 Order of vanishing / local multiplicity — **PRESENT**

- `analyticOrderAt`, `analyticOrderNatAt` — `Analysis/Analytic/Order.lean:48, 62`.
- Multiplicativity: `analyticOrderAt_mul`, `analyticOrderAt_smul` — lines 410, 243.
- Composition: `analyticOrderAt_comp` — line 441.
- Derivative shift: `AnalyticAt.analyticOrderAt_deriv_add_one` — line 263.

### 5.3 Isolated zeros and identity theorem — **PRESENT**

- `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` — IsolatedZeros.lean.
- `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` — IsolatedZeros.lean:242.

### 5.4 Open mapping — **PRESENT**

- `AnalyticAt.eventually_constant_or_nhds_le_map_nhds` —
  `Analysis/Analytic/OpenMapping.lean:119`.
- `AnalyticOnNhd.is_constant_or_isOpen` — line 166.

### 5.5 Covering maps / polynomials — **PRESENT**

- `IsCoveringMap`, `IsCoveringMapOn` — `Topology/Covering/Basic.lean`.
- `Complex.isCoveringMap_exp` — `Analysis/Complex/CoveringMap.lean:40`.
- `Polynomial.isCoveringMapOn_eval` — line 54.
- `isCoveringMapOn_npow` — line 63.

### 5.6 Branched cover / ramification index (geometric) — **ABSENT**

- `Ideal.ramificationIdx` — `NumberTheory/RamificationInertia/Basic.lean:19` —
  is number-theoretic, not connected to geometric maps between surfaces.
- No `IsBranchedCovering`, no ramification-index concept tied to
  `ContMDiff … ω` holomorphic maps.

### 5.7 Finite fibers for nonconstant holomorphic compact → compact — **ABSENT**

- Not packaged. Follows in principle from §5.3 + §5.4 + compactness, but no
  direct theorem.

### 5.8 Topological / Brouwer / winding-number degree — **ABSENT**

- No `Brouwer.degree`, no `windingNumber`, no `LocalDegree`.
- No `ContMDiff.degree` of a map between Riemann surfaces.

---

## 6. Verdict and Order of Attack

The period-lattice route `Jacobian X = H⁰(X, Ω¹)^∨ / H₁(X, ℤ)` remains the
intended default, but the inventory changes the **order of attack** and
sharpens the cost estimates in `plan.md`.

### Layers in roughly bottom-up build order

1. **Complex torus** — Phase 1. Blockers: §2.3 and §2.4 (the quotient
   manifold / LieAddGroup instance). Lattice and topological-quotient inputs
   are ready.
2. **Differential forms on manifolds** — Phase 2. Type does not exist
   (§3.4). Extensively bootstrappable from tangent bundle + smooth sections +
   alternating maps + normed-space `extDeriv`.
3. **Holomorphic 1-forms and finite-dimensionality** — Phase 2. Requires
   layer 2, then a serious Riemann-surface theorem (§3.5).
4. **Path and cycle integration on manifolds** — Phase 3. Most costly
   layer: no type takes a path in a manifold and a 1-form (§4.2); Stokes on
   manifolds is absent (§4.5).
5. **Singular homology of a compact surface** — Phase 3. Definition is in
   place (§4.3) but no concrete computation. Hurewicz (§4.4) is absent but
   could be a cheaper workaround than developing full singular-chain
   computation from the category-theoretic definition.
6. **Period lattice and Jacobian** — Phase 4. Lattice-in-a-f.d.-space API
   (§2.1) is ready to host the image once §4 exists.
7. **Abel-Jacobi** — Phase 5. Needs §4 plus path-independence.
8. **Degree, trace, pushforward/pullback** — Phases 6–7. Local holomorphic
   input is mostly PRESENT (§5.1–5.5); branched-cover degree is ABSENT
   (§5.6–5.8) but feasible as a definition-level addition on top of
   `analyticOrderAt` + compactness.

### Which "anti-hack" theorems are most at risk

- `ofCurve_inj` depends on layers 4–7; blocked until the integration layer
  exists.
- `pushforward_pullback` depends on layers 7 and 8; the trace-of-forms
  approach from `plan.md` needs the forms type (layer 2) first.
- `genus_eq_zero_iff_homeo` depends on finite-dimensionality of `H⁰(X, Ω¹)`
  (layer 3) **and** a classification theorem (uniformization or Riemann-Roch
  +construction of a degree-one meromorphic function). Outside layer 3, this
  is an entirely separate project.

### Candidate files to extend in Mathlib

- `Mathlib/Geometry/Manifold/Algebra/LieGroup.lean` (add quotient LieGroup).
- `Mathlib/Geometry/Manifold/ChartedSpace.lean` (add quotient ChartedSpace).
- `Mathlib/Geometry/Manifold/Complex.lean` (complex-manifold forms; already
  has a TODO listing exactly what we need).
- A new `Mathlib/Geometry/Manifold/DifferentialForm/` directory (forms
  definition, pullback, exterior derivative).
- A new `Mathlib/Geometry/Manifold/Integration/` directory (paths → forms,
  Stokes).
- `Mathlib/AlgebraicTopology/SingularHomology/` (Hurewicz, fundamental
  class, cap product, computations).
- `Mathlib/Analysis/Complex/BranchedCover.lean` (new: branched-cover degree
  for holomorphic maps between compact Riemann surfaces).

### Pin / commit housekeeping

- `Challenge.lean` references commit `8e3c989...` (15 Apr 2026). `lake-manifest`
  pins `v4.28.0` = `8f9d9cff...`. Confirm `Challenge.lean` builds against the
  pinned manifest, or re-pin to the commit Kevin tested.

---

## 7. Snapshot Tables

### 7.1 Status by plan.md Phase 0.5 checklist

| # | Item | Status | Primary file(s) |
|---|------|--------|-----------------|
| 1 | Quotient manifolds by discrete group actions | ABSENT | — |
| 2 | Charted-space / manifold instances for quotients | ABSENT | — |
| 3 | Topological group quotients by additive subgroups | PARTIAL | Topology/Algebra/Group/Quotient.lean |
| 4 | Finite-dim real / complex lattices | PRESENT | Algebra/Module/ZLattice/Basic.lean |
| 5 | Smooth differential forms on manifolds | ABSENT | — |
| 6 | Holomorphic differential forms on complex manifolds | ABSENT | — |
| 7 | Exterior derivative + closedness on manifolds | ABSENT (normed-space only) | Analysis/Calculus/DifferentialForm/Basic.lean |
| 8 | Integration of 1-forms along paths (manifolds) | ABSENT (normed-space only) | MeasureTheory/Integral/CurveIntegral/Basic.lean |
| 9 | Integration over chains / homology classes | ABSENT | — |
| 10 | Singular homology / cycle theory | PARTIAL | AlgebraicTopology/SingularHomology/Basic.lean |
| 11 | Local normal form for holomorphic maps | PRESENT | Analysis/Analytic/{IsolatedZeros,Order,OpenMapping}.lean |
| 12 | Local multiplicity / ramification / finite-fiber | PARTIAL | Analysis/Analytic/Order.lean; Topology/Covering/Basic.lean |

### 7.2 Quick-reference list of Mathlib names to depend on

PRESENT and directly usable:

- `ChartedSpace`, `IsManifold`, `contDiffGroupoid`
- `ContMDiff`, `ContMDiffWithinAt`, `contMDiff_id`
- `LieAddGroup`, `ContMDiffAdd`, `ContinuousAddMonoidHom` (`→ₜ+`)
- `modelWithCornersSelf`, `𝓘(𝕜)`, `𝓘(𝕜, E)`
- `IsZLattice`, `ZSpan.fundamentalDomain`, `ZLattice.basis`
- `QuotientAddGroup.mk`, `QuotientGroup.instTopologicalSpace`,
  `QuotientGroup.instCompactSpace`
- `AlternatingMap`, `ContinuousAlternatingMap`, `ExteriorAlgebra`
- `TangentBundle`, `ContMDiffSection`
- `analyticOrderAt`, `analyticOrderNatAt`
- `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`
- `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`
- `AnalyticOnNhd.is_constant_or_isOpen`
- `IsCoveringMap`, `Polynomial.isCoveringMapOn_eval`
- `extDeriv`, `extDerivWithin`, `extDeriv_extDeriv`
- `curveIntegral`, `curveIntegral_trans`, `curveIntegral_symm`
- `Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable`
- `singularChainComplexFunctor`, `singularHomologyFunctor`
- `FundamentalGroup`, `FundamentalGroupoid`

Named gaps that need to be created:

- `ChartedSpace` / `IsManifold` / `LieAddGroup` instance on `V ⧸ Λ`
- `MDifferentialForm`, `HolomorphicOneForm`, manifold `extDeriv`
- Path integral on a manifold / `∫_γ ω` for `γ : C([0,1], X)`
- Stokes on a compact manifold with boundary
- Hurewicz `π₁^{ab} → H₁`
- `FiniteDimensional ℂ (HolomorphicOneForm X)` on a compact Riemann surface
- `ContMDiff.degree` for holomorphic maps between compact Riemann surfaces
  (via `analyticOrderAt`-based local degree summed over fibers)
- `IsManifold 𝓘(ℂ) ω (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)`, if
  the sphere ever has to be compared to `X` as a complex manifold rather
  than only topologically
