import Jacobian.HolomorphicForms.RiemannRoch

/-!
# Degree of meromorphic maps to the Riemann sphere

This module names the second production interface needed by the genus-zero
classification proof: a meromorphic map with pole divisor `[P]` promotes to a
continuous bijection `X → OnePoint ℂ`.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/-- Degree data for a meromorphic map to the Riemann sphere.

The current downstream consumer only needs continuity and bijectivity.  The
`degree_eq_pole_degree` field records the future divisor-degree theorem that
explains why these consequences hold. -/
structure MeromorphicDegreeOneData
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X) where
  continuous_toMap : Continuous f.toMap
  bijective_toMap : Function.Bijective f.toMap
  degree_eq_pole_degree : Divisor.degree f.poles = 1

/-- **Degree/pole-divisor leaf.** A meromorphic map whose pole divisor is
`[P]` has degree one and therefore is continuous and bijective as a map to
`OnePoint ℂ`.

Bottom-up content: prove the extension/removable-singularity theorem,
properness from compactness, and the theorem that the map degree equals the
degree of the pole divisor. -/
theorem meromorphicDegreeOneData_of_poleDivisor_point
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicMapToSphere X) (P : X)
    (hpole : f.poles = Divisor.point P) :
    Nonempty (MeromorphicDegreeOneData X f) := by
  sorry

end JacobianChallenge.HolomorphicForms
