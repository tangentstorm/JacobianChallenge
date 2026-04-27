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
