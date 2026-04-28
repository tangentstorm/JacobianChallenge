import Jacobian.HolomorphicForms.AnalyticGenus
import Jacobian.HolomorphicForms.OnePointCxIsManifold
import Jacobian.HolomorphicForms.Ext
import Jacobian.HolomorphicForms.EntireZero
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Genus-zero classification

A compact connected Riemann surface has analytic genus zero iff it is
homeomorphic to the standard 2-sphere `Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1`.

Proof deferred — this is the genus-zero classification (uniformization
theorem / Riemann–Roch + classification of compact connected oriented
surfaces). One of the project's anti-hack theorems.

Top-down obligation: pointed to by `Jacobian/Solution.lean` for the
`genus_eq_zero_iff_homeo` lemma.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/-!
### Blocker analysis for `analyticGenus_eq_zero_of_homeomorphic_sphere`

**Status (2026-04-27):** sorry — all three required ingredients are absent
from Mathlib v4.28.0 (commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`).

#### Proof sketch

1. **Uniqueness of smooth structure on S².** Every topological 2-sphere
   admits a unique smooth structure up to diffeomorphism (Radó 1925 /
   Morse 1960). Given `X ≃ₜ S²`, transfer the smooth structure on `X`
   (from its complex charts) to `S²` and apply uniqueness to get a
   *diffeomorphism* `X ≃ₘ S²`.
   - **Mathlib gap:** No `SmoothManifoldWithCorners` structure on
     `Metric.sphere … 1` in `ℝ³`; no smooth classification of compact
     surfaces; no `Diffeomorph` between abstract smooth manifolds and
     concrete spheres. Searched: `ComplexProjectiveLine`,
     `RiemannSphere`, `cotangentSpace_finrank` — all absent.

2. **Uniqueness of complex structure on S².** A smooth compact oriented
   2-manifold diffeomorphic to `S²` carries a unique complex structure up
   to biholomorphism (consequence of the uniformization theorem: every
   simply connected Riemann surface is biholomorphic to `ℂ`, `𝔻`, or
   `ℂℙ¹`; compactness forces `ℂℙ¹`). So `X` is biholomorphic to `ℂℙ¹`.
   - **Mathlib gap:** No uniformization theorem; no `ℂℙ¹` as a complex
     manifold; no biholomorphism API for Riemann surfaces.

3. **H⁰(ℂℙ¹, Ω¹) = 0.** On `ℂℙ¹`, the canonical sheaf `Ω¹` has
   degree `−2`. A line bundle of negative degree on a compact Riemann
   surface has no nonzero global sections. Hence the space of holomorphic
   1-forms is trivial and `analyticGenus = 0`.
   - **Mathlib gap:** No sheaf-cohomology or divisor-degree theory; no
     definition of `ℂℙ¹` as a Riemann surface; no Riemann–Roch theorem.

#### Lemmas searched in Mathlib (all absent)

- `ComplexProjectiveLine` / `RiemannSphere` — not defined.
- `Diffeomorph.ofHomeomorphSphere` — no smooth classification of surfaces.
- `cotangentSpace_finrank` — no dimension computation for cotangent spaces.
- `Module.finrank_holomorphicOneForms_sphere` — not available.
- `IsManifold.sphere` (for `Metric.sphere` in `ℝ³` with `ℂ`-charts) — absent.

#### Dependency graph blocker

```
analyticGenus_eq_zero_of_homeomorphic_sphere
  │
  ├─► [MISSING] smooth_structure_unique_on_S2
  │     └─► [MISSING] IsManifold instance for Metric.sphere in ℝ³
  │
  ├─► [MISSING] complex_structure_unique_on_S2
  │     └─► [MISSING] uniformization_theorem
  │           └─► [MISSING] ℂℙ¹ as complex manifold
  │
  └─► [MISSING] holomorphicOneForms_CP1_subsingleton
        ├─► [MISSING] ℂℙ¹ definition + ChartedSpace instance
        ├─► [MISSING] canonical_sheaf_degree_CP1 = -2
        └─► [MISSING] negative_degree_line_bundle_no_sections
```

#### 3-step Mathlib-API plan for a future job

**Step 1 — Define `ℂℙ¹` as a complex manifold.**
Define `ℂℙ¹` (e.g. as `Projectivization ℂ (Fin 2 → ℂ)` or as the
one-point compactification `AlexandrovCompactification ℂ`). Equip it
with `ChartedSpace ℂ` and `IsManifold` instances using the standard
two-chart atlas (`z ↦ z`, `z ↦ 1/z`). Prove it is compact, connected,
T2, and homeomorphic to `Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1`.

**Step 2 — Compute `H⁰(ℂℙ¹, Ω¹) = 0` directly.**
Bypass the general Riemann–Roch machinery: show that any holomorphic
1-form on `ℂℙ¹` restricts to `f(z) dz` on the standard chart `U₀ ≅ ℂ`,
and the transition to the chart `U₁` forces `f(z) = 0` (by Liouville's
theorem applied to the resulting entire function with growth constraint).
Conclude `Subsingleton (HolomorphicOneForm ℂ ℂℙ¹)`.

**Step 3 — Transport along homeomorphism.**
For compact Riemann surfaces `X ≃ₜ ℂℙ¹`, the homeomorphism lifts to a
biholomorphism (by uniqueness of complex structure on `S²`), giving an
isomorphism of 1-form spaces. Transport the subsingleton result from
Step 2 to `X` and apply `analyticGenus_eq_zero_of_subsingleton`.

An alternative shortcut for **Step 3** (avoiding uniformization): if
we only need genus 0, prove directly that `Module.finrank` of sections
of a bundle is invariant under biholomorphism, and show the
homeomorphism `X ≃ₜ S²` lifts to a biholomorphism `X ≃ₕ ℂℙ¹` using
the fact that every orientation-preserving homeomorphism between
Riemann surfaces is homotopic to a biholomorphism (Earle–Eells).
-/

/-! ### Refined decomposition of the easy direction

The easy direction `analyticGenus_eq_zero_of_homeomorphic_sphere` is now
assembled from three smaller named obligations, each Aristotle-shaped:

* `holomorphicOneForm_onePointCx_subsingleton` — the space of holomorphic
  1-forms on `ℂℙ¹ = OnePoint ℂ` is a subsingleton (i.e. only the zero
  form exists).  This is the substantive analytic content
  (Liouville-style argument on the inversion chart).
* `analyticGenus_onePointCx_eq_zero` — pure corollary of the subsingleton
  fact via `analyticGenus_eq_zero_of_subsingleton`.
* `analyticGenus_eq_of_homeomorphic_sphere_of_onePointCx` — the
  uniformization-lite transport step: a compact Riemann surface
  homeomorphic to `S²` has the same analytic genus as `OnePoint ℂ`.
  This bundles the deep "every complex structure on `S²` is biholomorphic
  to `ℂℙ¹`" content into a single named obligation.

The original `analyticGenus_eq_zero_of_homeomorphic_sphere` becomes pure
assembly of these three pieces. The hard direction
`homeomorphic_sphere_of_analyticGenus_eq_zero` below is unchanged.
-/

/-! #### Proof plan for `holomorphicOneForm_onePointCx_subsingleton`

A holomorphic 1-form on `OnePoint ℂ` pulled back to
the identity chart is `f(z) dz` for some entire function `f : ℂ → ℂ`;
under the inversion-chart transition `w = z⁻¹`, it becomes
`-f(1/w) / w² dw`. Holomorphicity at `w = 0` forces `f(1/w) / w²` to be
bounded near zero, which by Liouville's theorem forces `f ≡ 0`.

This is decomposed into:
1. `entire_tendsto_zero_eq_zero` — Liouville-based vanishing of entire
   functions that tend to 0 at infinity.
2. `holomorphicOneForm_onePointCx_toFun_eq_zero` — the chart-level
   argument showing every 1-form evaluates to zero at every point.
3. `holomorphicOneForm_onePointCx_subsingleton` — pure assembly. -/

/-- An entire function `f : ℂ → ℂ` that tends to `0` along `cocompact ℂ`
(i.e. as `|z| → ∞`) is identically zero.

This is the Liouville-application building block of the Liouville core.
The proof is provided sorry-free in
`Jacobian/HolomorphicForms/EntireZero.lean` as
`Differentiable.eq_zero_of_tendsto_zero_cocompact`. -/
theorem entire_tendsto_zero_eq_zero (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h : Filter.Tendsto f (Filter.cocompact ℂ) (nhds 0)) :
    f = 0 :=
  hf.eq_zero_of_tendsto_zero_cocompact h

/-- Every holomorphic 1-form on `OnePoint ℂ` (= ℂℙ¹) evaluates to zero
at every point.

**Proof sketch.** The fiber `CotangentSpace ℂ (OnePoint ℂ) x` is
`TangentSpace 𝓘(ℂ,ℂ) x →L[ℂ] ℂ`, which is definitionally `ℂ →L[ℂ] ℂ`.
An element of `ℂ →L[ℂ] ℂ` is determined by its value at `1 : ℂ`
(multiplication by a scalar). So a holomorphic 1-form `ω` defines a
function `f : ℂ → ℂ` by `f(z) = (ω.toFun (↑z)) 1`.

1. **`f` is entire.** The section `ω` is `ContMDiff ⊤` on `OnePoint ℂ`.
   On the identity chart (source `{∞}ᶜ ≅ ℂ`), reading the section through
   the tangent bundle trivialization gives a `ContDiff ℂ ⊤` map `ℂ → ℂ →L[ℂ] ℂ`,
   and composing with evaluation at `1` gives a differentiable `f : ℂ → ℂ`.

2. **`f(z) → 0` as `|z| → ∞`.** On the inversion chart (source `{↑0}ᶜ`,
   forward map `∞ ↦ 0`, `↑z ↦ z⁻¹`), the chart transition sends
   `f(z) dz` to `g(w) dw` where `g(w) = -f(w⁻¹) · w⁻²`. For `ω` to be
   smooth at `∞`, the function `g` must extend `ContDiff` across `w = 0`.
   In particular `g(w) → g(0)` as `w → 0`, forcing
   `|f(w⁻¹)| = |g(w)| · |w|² → 0` as `w → 0`, i.e. `f(z) → 0` as `|z| → ∞`.

3. **Liouville.** Apply `entire_tendsto_zero_eq_zero` to conclude `f = 0`,
   hence `ω.toFun (↑z) = 0` for all finite `z`. Continuity of the section
   gives `ω.toFun ∞ = 0` as well.

**Mathlib gap:** Steps 1–2 require reading a `ContMDiffSection` of the
cotangent bundle through chart trivializations and extracting the local
coefficient function. The tangent/cotangent bundle trivialization API in
Mathlib v4.28.0 does not provide convenient lemmas for this extraction
on concrete manifolds like `OnePoint ℂ`. Specifically:
- No lemma gives the local representation of a `ContMDiffSection` of
  `Bundle.ContinuousLinearMap` in terms of a function on the chart domain.
- The chart transition formula for the cotangent bundle is not available
  in user-facing form.
- Connecting `ContMDiff` of the section to `Differentiable` of the
  coefficient function requires composing the vector bundle trivialization
  with the manifold chart and unwinding several layers of bundled structure. -/
theorem holomorphicOneForm_onePointCx_toFun_eq_zero
    (ω : HolomorphicOneForm ℂ (OnePoint ℂ)) (x : OnePoint ℂ) :
    ω.toFun x = 0 := by sorry

theorem holomorphicOneForm_onePointCx_subsingleton :
    Subsingleton (HolomorphicOneForm ℂ (OnePoint ℂ)) :=
  ⟨fun a b => ext_toFun (fun x => by
    rw [holomorphicOneForm_onePointCx_toFun_eq_zero a x,
        holomorphicOneForm_onePointCx_toFun_eq_zero b x])⟩

/-- An auxiliary `FiniteDimensionalHolomorphicOneForms` instance on
`OnePoint ℂ`, derived from the subsingleton fact above.  Needed in
order to apply the `analyticGenus` definition.

A subsingleton module is trivially finite-dimensional (the empty set is
a spanning set), so this is purely a typeclass-level lemma. -/
noncomputable instance finiteDimensionalHolomorphicOneForms_onePointCx :
    FiniteDimensionalHolomorphicOneForms ℂ (OnePoint ℂ) where
  finiteDimensional := by
    haveI : Subsingleton (HolomorphicOneForm ℂ (OnePoint ℂ)) :=
      holomorphicOneForm_onePointCx_subsingleton
    refine ⟨?_⟩
    -- A subsingleton module has `⊤ = ⊥`, and `⊥` is finitely generated.
    have htop : (⊤ : Submodule ℂ (HolomorphicOneForm ℂ (OnePoint ℂ))) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x _
      exact Subsingleton.elim x 0
    rw [htop]
    exact Submodule.fg_bot

/-- The analytic genus of `OnePoint ℂ` (= ℂℙ¹) is zero.

Pure corollary of `holomorphicOneForm_onePointCx_subsingleton` via
`analyticGenus_eq_zero_of_subsingleton`. -/
theorem analyticGenus_onePointCx_eq_zero :
    analyticGenus ℂ (OnePoint ℂ) = 0 := by
  haveI : Subsingleton (HolomorphicOneForm ℂ (OnePoint ℂ)) :=
    holomorphicOneForm_onePointCx_subsingleton
  exact analyticGenus_eq_zero_of_subsingleton

/-- Transport step: a compact Riemann surface `X` homeomorphic to the
standard 2-sphere has the same analytic genus as `OnePoint ℂ`.

This is the "uniformization-lite" content: a topological homeomorphism
from `X` to `S²`, combined with the existing complex structure on `X`
and the canonical complex structure on `OnePoint ℂ` (from
`OnePointCxIsManifold`), forces a biholomorphism `X ≃ OnePoint ℂ` (since
every complex structure on the topological 2-sphere is biholomorphic to
`ℂℙ¹` — uniformization at genus 0). The biholomorphism induces a
ℂ-linear isomorphism of holomorphic 1-form spaces, hence equality of
analytic genera.

Stated as an equality of natural numbers, since both sides are defined
once their `FiniteDimensionalHolomorphicOneForms` instances are
available (`X`'s comes from the hypothesis, `OnePoint ℂ`'s comes from
`finiteDimensionalHolomorphicOneForms_onePointCx` above).

Bottom-up content for a future job: build a complex-structure-transfer
API for homeomorphisms between Riemann surfaces (Mathlib gap), or — more
realistically — go via `onePointCxHomeoS2` and the uniqueness of complex
structure on `S²` (deep, see the survey above). -/
theorem analyticGenus_eq_of_homeomorphic_sphere_of_onePointCx
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (_h : Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    analyticGenus ℂ X = analyticGenus ℂ (OnePoint ℂ) := sorry

/-- The "easy" direction: if `X` is homeomorphic to the standard 2-sphere
then `analyticGenus ℂ X = 0`.

Pure assembly of `analyticGenus_eq_of_homeomorphic_sphere_of_onePointCx`
(the uniformization-lite transport step) and
`analyticGenus_onePointCx_eq_zero` (the analytic core
`H⁰(ℂℙ¹, Ω¹) = 0`).

Bottom-up content: a compact Riemann surface homeomorphic to `S²` has
the complex structure of `ℂℙ¹` (every smooth structure on `S²` is unique,
and the complex structure on a smooth compact 2-manifold is determined by
its conformal class which is unique on `S²`); on `ℂℙ¹` the canonical
sheaf has degree `-2 < 0`, so `H⁰(ℂℙ¹, Ω¹) = 0` by elementary
divisor-degree considerations. -/
theorem analyticGenus_eq_zero_of_homeomorphic_sphere
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (h : Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    analyticGenus ℂ X = 0 := by
  rw [analyticGenus_eq_of_homeomorphic_sphere_of_onePointCx X h]
  exact analyticGenus_onePointCx_eq_zero

/-!
### Blocker analysis for `homeomorphic_sphere_of_analyticGenus_eq_zero`

**Status (2026-04-27):** sorry — all core ingredients are absent from
Mathlib v4.28.0 (commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`).
This is strictly harder than the easy direction; it requires the
*forward* implication of uniformization at genus 0.

#### Mathematical content

A compact connected Riemann surface `X` with `analyticGenus ℂ X = 0`
(i.e. `H⁰(X, Ω¹) = 0`, equivalently
`Subsingleton (HolomorphicOneForm ℂ X)` by
`analyticGenus_eq_zero_iff_subsingleton`) is homeomorphic to `S²`.

The standard proof runs through the following chain:

1. **Genus 0 ⟹ simply connected.** By the topological classification
   of compact oriented surfaces, the topological genus equals the
   analytic genus (Hodge theory / de Rham). A compact oriented surface
   of topological genus 0 is simply connected.

2. **Simply connected compact Riemann surface ⟹ biholomorphic to ℂℙ¹.**
   The uniformization theorem says every simply connected Riemann surface
   is biholomorphic to ℂ, 𝔻, or ℂℙ¹. Compactness rules out ℂ and 𝔻.

3. **ℂℙ¹ ≃ₜ S².** The one-point compactification of ℂ (= ℂℙ¹ as a
   topological space) is homeomorphic to the standard 2-sphere in ℝ³
   via stereographic projection.

An alternative route avoids uniformization entirely by using Riemann–Roch
+ a rational function argument:

1'. **Genus 0 + Riemann–Roch ⟹ ∃ meromorphic function of degree 1.**
    With `g = 0`, Riemann–Roch gives `ℓ(D) - ℓ(K-D) ≥ deg D + 1` for
    any divisor `D`. Taking `D` = a single point gives a meromorphic
    function with a single simple pole, i.e. of degree 1.

2'. **Degree-1 meromorphic function ⟹ biholomorphism to ℂℙ¹.**
    A meromorphic function of degree 1 on a compact Riemann surface is a
    biholomorphism onto ℂℙ¹.

3'. Same as step 3.

#### Mathlib API survey

| Concept searched | Found? | Notes |
|---|---|---|
| `uniformization` | ❌ | No uniformization theorem in any form. |
| `RiemannSurface` | ❌ | No dedicated Riemann surface type. |
| `ComplexProjectiveLine` / `RiemannSphere` | ❌ | Not defined as a type or manifold. |
| `Projectivization` | ✅ | `Projectivization ℂ (Fin 2 → ℂ)` exists but has no manifold or complex-analytic structure. |
| `OnePoint` (one-point compactification) | ✅ | `OnePoint ℂ` exists, is `CompactSpace`, but has no `T2Space`, `ChartedSpace`, or `IsManifold` instance. No homeomorphism to `Metric.sphere`. |
| `stereographic` / `stereographic'` | ✅ | Stereographic projection exists for `Metric.sphere (0 : E) 1` in a real inner product space `E`. Gives `ChartedSpace (EuclideanSpace ℝ (Fin n))` and `IsManifold (𝓡 n)` for the `n`-sphere in `ℝⁿ⁺¹`. The 2-sphere is charted over `EuclideanSpace ℝ (Fin 2)`, **not** over `ℂ`. |
| `EuclideanSpace.instChartedSpaceSphere` | ✅ | Gives `ChartedSpace (EuclideanSpace ℝ (Fin 2))` on `Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1`. The model is *real*, not complex. |
| `IsManifold` for sphere | ✅ | `IsManifold (𝓡 2) ⊤` on `S²` exists (real smooth manifold). No complex manifold instance. |
| `SimplyConnectedSpace` | ✅ | Class exists. No instance for `S²` or `OnePoint ℂ`. |
| `IsCoveringMap` | ✅ | Covering map API exists with path-lifting. No universal covering construction for Riemann surfaces. |
| `MeromorphicAt` | ✅ | Pointwise meromorphic function API exists (orders, trailing coefficients). No global meromorphic function type on manifolds; no divisor theory. |
| `Divisor` / `RiemannRoch` | ❌ | No divisor theory, no Riemann–Roch theorem. |
| `Hodge` / `deRham` / `topologicalGenus` | ❌ | No Hodge theory, no de Rham cohomology, no topological genus. |
| `Homeomorph.compactificationToSphere` | ❌ | No homeomorphism `OnePoint ℂ ≃ₜ S²`. |
| `EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ` | Partial | `Complex.measurableEquiv` and `Complex.isometry_ofReal` exist but a full `LinearIsometryEquiv` from `EuclideanSpace ℝ (Fin 2)` to `ℂ` is not directly available as a named lemma. |

#### Dependency graph

```
homeomorphic_sphere_of_analyticGenus_eq_zero
  │
  ├─► analyticGenus_eq_zero_iff_subsingleton  [AVAILABLE ✅]
  │     (converts hypothesis to Subsingleton (HolomorphicOneForm ℂ X))
  │
  ├─► [MISSING ❌] genus_zero_implies_simply_connected
  │     ├─► [MISSING ❌] analytic_genus_eq_topological_genus (Hodge theory)
  │     │     ├─► [MISSING ❌] de Rham cohomology
  │     │     └─► [MISSING ❌] Hodge decomposition
  │     └─► [MISSING ❌] topological classification of compact oriented surfaces
  │           └─► [MISSING ❌] surface_genus_zero_iff_simply_connected
  │
  ├─► [MISSING ❌] uniformization_compact_simply_connected
  │     ├─► [MISSING ❌] uniformization_theorem
  │     │     ├─► [MISSING ❌] universal covering of Riemann surface
  │     │     ├─► [MISSING ❌] Riemann mapping theorem (for ℂ and 𝔻)
  │     │     └─► [MISSING ❌] Koebe's theorem / Perron's method
  │     └─► [MISSING ❌] compactness rules out ℂ and 𝔻
  │
  ├─► [MISSING ❌] CP1_def : ℂℙ¹ as a complex manifold
  │     ├─► [PARTIAL] Projectivization ℂ (Fin 2 → ℂ) (no manifold structure)
  │     └─► [PARTIAL] OnePoint ℂ (no T2, no manifold structure)
  │
  └─► [MISSING ❌] CP1_homeomorph_sphere : ℂℙ¹ ≃ₜ S²
        ├─► [PARTIAL] stereographic / stereographic' (real model only)
        └─► [MISSING ❌] OnePoint ℂ ≃ₜ Metric.sphere 0 1 in ℝ³
```

**Alternative route via Riemann–Roch:**

```
homeomorphic_sphere_of_analyticGenus_eq_zero
  │
  ├─► [AVAILABLE ✅] analyticGenus_eq_zero_iff_subsingleton
  │
  ├─► [MISSING ❌] riemann_roch_genus_zero_degree_one_function
  │     ├─► [MISSING ❌] Riemann–Roch theorem
  │     │     ├─► [MISSING ❌] sheaf cohomology on Riemann surfaces
  │     │     └─► [MISSING ❌] Serre duality
  │     └─► [MISSING ❌] divisor theory
  │
  ├─► [MISSING ❌] degree_one_meromorphic_iff_biholomorphic_CP1
  │     └─► [MISSING ❌] global meromorphic functions on manifolds
  │
  └─► [MISSING ❌] CP1_homeomorph_sphere (same as above)
```

#### 3-step Mathlib-API plan for a future job

**Step 1 — Build `ℂℙ¹` as a complex manifold and prove `ℂℙ¹ ≃ₜ S²`.**

Define `ℂℙ¹` as `OnePoint ℂ` (the Alexandrov one-point compactification
of `ℂ`). Equip it with:
- A `T2Space` instance (requires locally compact + T2 of `ℂ`, which
  Mathlib already has).
- A `ChartedSpace ℂ` instance via two charts: `z ↦ z` on `ℂ ⊂ OnePoint ℂ`
  and `z ↦ 1/z` on `(OnePoint ℂ) \ {0}`.
- An `IsManifold (modelWithCornersSelf ℂ ℂ) ⊤` instance by showing chart
  transitions are holomorphic (they are `z ↦ 1/z` on `ℂ \ {0}`).
- A `Homeomorph` from `OnePoint ℂ` to `Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1`
  by composing the identification `ℂ ≅ ℝ²` with the inverse of
  stereographic projection and extending continuously to the point at
  infinity.

**Estimated difficulty:** Medium-hard. The topological parts (compact,
connected, T2) are close to what Mathlib has for `OnePoint`. The main
work is constructing the complex atlas and proving the homeomorphism
with `S²`. The latter requires showing that `stereographic'⁻¹ ∘ (ℂ → ℝ²)`
extends continuously to a bijection `OnePoint ℂ → S²`. Roughly 300–600
lines of new Lean code.

**Step 2 — Prove `H⁰(ℂℙ¹, Ω¹) = 0` directly (no Riemann–Roch).**

Show `Subsingleton (HolomorphicOneForm ℂ (OnePoint ℂ))` by a direct
argument: a holomorphic 1-form on `OnePoint ℂ` restricts to `f(z) dz`
on the standard chart `ℂ`, where `f : ℂ → ℂ` is entire. On the chart at
infinity, the transition gives `f(z) dz = -f(1/w) / w² dw`, which must
be holomorphic at `w = 0`. By Liouville's theorem (available in Mathlib:
`Complex.liouville_theorem`), `f` is constant, and the holomorphicity
condition at infinity forces the constant to be zero.

**Estimated difficulty:** Medium. Liouville's theorem is available.
The main challenge is formalizing what "holomorphic 1-form on a charted
space" means in terms of the chart transition — this depends on the
project's `HolomorphicOneForm` API and may require additional interface
lemmas.

**Step 3 — The actual uniformization step (genus 0 ⟹ biholomorphic to ℂℙ¹).**

This is the hardest step and has two possible sub-approaches:

**(3a) Via uniformization theorem (very hard).** Prove the uniformization
theorem for compact Riemann surfaces: every simply connected Riemann
surface is biholomorphic to ℂ, 𝔻, or ℂℙ¹. This is a major theorem
requiring Perron's method, Dirichlet problem on Riemann surfaces,
normal families, and the Riemann mapping theorem. Estimated at 2000+
lines of new Lean code. Then show `genus 0 ⟹ simply connected`
(requires Hodge theory or classification of surfaces).

**(3b) Via Riemann–Roch (hard).** Prove the Riemann–Roch theorem for
compact Riemann surfaces. Then the argument is: genus 0 ⟹ degree-1
meromorphic function exists ⟹ biholomorphism to ℂℙ¹. This avoids
uniformization but requires sheaf cohomology, Serre duality, and
divisor theory. Estimated at 1500+ lines.

**(3c) Via direct Mittag-Leffler–style argument (moderately hard).**
Avoid both uniformization and full Riemann–Roch. Use the vanishing
of `H¹(X, 𝒪)` (which follows from `H⁰(X, Ω¹) = 0` by Serre duality —
but Serre duality itself is nontrivial). Then Mittag-Leffler–type
arguments produce a meromorphic function of degree 1. This still
requires substantial analytic machinery not in Mathlib.

#### Honest assessment

This theorem is **not realistically formalizable** with the current
Mathlib API (v4.28.0). The gap is enormous:

- **ℂℙ¹ as a complex manifold** does not exist. Building it (Step 1)
is a self-contained project of moderate size (~500 lines) and is the
only step that could plausibly be completed in a focused effort.

- **The uniformization theorem** (or any equivalent, such as
Riemann–Roch for Riemann surfaces) is entirely absent and represents
one of the deepest results in complex analysis / algebraic geometry.
No path through Mathlib's current API gets close.

- **The bridge from analytic genus to topological genus** (Hodge theory /
de Rham cohomology) is also absent. Without it, even the implication
"genus 0 ⟹ simply connected" cannot be stated.

- **Comparison with the easy direction:** the easy direction
(`analyticGenus_eq_zero_of_homeomorphic_sphere`) requires showing
`H⁰(ℂℙ¹, Ω¹) = 0`, which can be done with Steps 1–2 alone (no
uniformization). The hard direction additionally requires Step 3,
which is strictly more demanding.

**Verdict:** This theorem should be classified as a **Phase 4+ deferred
dependency**. It is a deep uniformization-level result. A realistic
formalization would require either (a) formalizing the uniformization
theorem from scratch (~2000+ lines of new Lean), or (b) formalizing
Riemann–Roch for compact Riemann surfaces (~1500+ lines). Neither is
feasible in the near term without a dedicated multi-month effort.

The sorry should remain. The `analyticGenus_eq_zero_iff_homeomorphic_sphere`
biconditional that assembles both directions will carry two sorries
(one from each direction) until the relevant Mathlib infrastructure
matures.

#### Nearest Mathlib footholds (for future work)

- `OnePoint` (one-point compactification): good starting point for
  defining `ℂℙ¹` topologically.
- `stereographic` / `stereographic'` / `EuclideanSpace.instChartedSpaceSphere`:
  real manifold structure on `S²`, needed for Step 1's homeomorphism.
- `Complex.liouville_theorem`: Liouville's theorem for bounded entire
  functions, needed for Step 2.
- `MeromorphicAt`: pointwise meromorphic function API, useful building
  block for Steps 2–3.
- `SimplyConnectedSpace`: the class exists, though no instance for `S²`.
- `IsCoveringMap` + path lifting: covering space theory, relevant if
  pursuing uniformization via universal covers.
-/

/-- The "hard" direction: if `analyticGenus ℂ X = 0` then `X` is
homeomorphic to the standard 2-sphere.

Bottom-up content: this is essentially a uniformization-level theorem.
Genus zero in the analytic sense means the space of holomorphic 1-forms
is `Subsingleton` (equivalently `Module.finrank ℂ … = 0`); together with
compactness and connectedness this forces `X` to be biholomorphic to
`ℂℙ¹` (uniformization theorem), and `ℂℙ¹` is homeomorphic to `S²` via
the standard stereographic charts. -/
theorem homeomorphic_sphere_of_analyticGenus_eq_zero
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (_h : analyticGenus ℂ X = 0) :
    Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := sorry

/-- A compact connected Riemann surface has analytic genus zero iff it is
homeomorphic to the standard 2-sphere.

Pure assembly of the two directions
`analyticGenus_eq_zero_of_homeomorphic_sphere` and
`homeomorphic_sphere_of_analyticGenus_eq_zero`; this declaration adds
no new sorry. -/
theorem analyticGenus_eq_zero_iff_homeomorphic_sphere
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    analyticGenus ℂ X = 0 ↔
      Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  ⟨homeomorphic_sphere_of_analyticGenus_eq_zero X,
   analyticGenus_eq_zero_of_homeomorphic_sphere X⟩

end JacobianChallenge.HolomorphicForms