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

/-- A compact connected Riemann surface has analytic genus zero iff it is
homeomorphic to the standard 2-sphere.

Top-down obligation. Bottom-up: deep classical theorem requiring
uniformization or Riemann–Roch + classification of surfaces. -/
theorem analyticGenus_eq_zero_iff_homeomorphic_sphere
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    analyticGenus ℂ X = 0 ↔
      Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := sorry

end JacobianChallenge.HolomorphicForms
