import Jacobian.HolomorphicForms.FiniteDimensional

/-!
# Finite-dimensionality on a compact connected Riemann surface

The classical result that the space of holomorphic 1-forms on a compact
connected Riemann surface is finite-dimensional. Proof deferred — this is
one of the central analytic theorems on the bottom-up roadmap (Phase 2:
Riemann–Roch / Hodge / harmonic-form route).

This module is the named obligation pointed to by the top-down refinement
of `Solution.genus`.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/-!
### Mathlib Dependency Blocker & Future API Plan

Currently, this proof cannot be completed because Mathlib (v4.28.0) lacks the
foundational analytic machinery for holomorphic sections on manifolds.

**Mathlib lemmas tried:**
- `FiniteDimensional.of_locallyCompactSpace` and `FiniteDimensional.proper` (Riesz's theorem):
  To apply these, we would need a topology on `HolomorphicOneForm`.
- `FiniteDimensional.of_locallyCompact_manifold`: Not applicable since our space of sections
  is not naturally modeled as a manifold itself unless infinite-dimensional.
- Searched for `MontelSpace` and `ArzelaAscoli.compactSpace_of_isClosedEmbedding` but
  they require pre-existing topologies on function spaces.

**What the dependency graph blocked on:**
1. **Topology on sections:** There is no `TopologicalSpace` or `NormedSpace`
   instance for `ContMDiffSection` (which `HolomorphicOneForm` is a special case of)
   in Mathlib yet.
2. **Compactness theorems:** We lack Montel's theorem for families of holomorphic
   sections, or alternatively, Hodge theory / elliptic regularity for the $\bar{\partial}$
   operator on manifolds.
3. **Complex geometry:** We lack Riemann-Roch, Serre duality, or the uniformization
   theorem which would allow pulling back to a covering disc to apply Cauchy estimates.

**3-Step Mathlib-API Plan for a future job:**
1. **Topological Structure:** Define the topology of uniform convergence on compact
   sets for `ContMDiffSection`, and upgrade it to a Banach space structure when the
   base manifold is `CompactSpace`.
2. **Montel's Theorem / Elliptic Regularity:** Prove that for holomorphic sections
   over a compact complex manifold, bounded subsets in the supremum norm are
   relatively compact (by using local Cauchy estimates on charts).
3. **Riesz's Theorem:** Conclude by applying `FiniteDimensional.of_locallyCompactSpace`
   to the Banach space of global holomorphic sections. Since the unit ball is relatively
   compact, the space must be finite-dimensional.
-/

/-- On a compact connected Riemann surface (a compact connected 1-dimensional
complex manifold), the space of holomorphic 1-forms is finite-dimensional.

Top-down obligation: pointed to by `Jacobian/Solution.lean` for the
`genus` declaration. Bottom-up: classical Riemann–Roch / Hodge theory. -/
instance compactRiemannSurface_finiteDimensionalHolomorphicOneForms
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    FiniteDimensionalHolomorphicOneForms ℂ X := sorry

end JacobianChallenge.HolomorphicForms
