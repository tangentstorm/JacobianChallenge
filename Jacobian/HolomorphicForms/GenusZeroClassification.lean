import Jacobian.HolomorphicForms.AnalyticGenus
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

/-- The "easy" direction: if `X` is homeomorphic to the standard 2-sphere
then `analyticGenus ℂ X = 0`.

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
    (_h : Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    analyticGenus ℂ X = 0 := sorry

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
