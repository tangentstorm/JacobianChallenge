import Jacobian.HolomorphicForms.AnalyticGenus
import Jacobian.HolomorphicForms.Meromorphic

/-!
# Riemann-Roch interface for the genus-zero route

This module exposes the first production theorem leaf needed by
`GenusZeroClassification.lean`: genus zero gives a meromorphic map with one
prescribed simple pole.  The eventual proof belongs here, built from divisor
theory and Riemann-Roch for compact Riemann surfaces.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/-- Fixed-pole Riemann-Roch output in genus zero. -/
structure GenusZeroFixedPoleMeromorphicData
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X)
    (_h : analyticGenus ℂ X = 0) where
  meromorphicMap : MeromorphicMapToSphere X
  poleDivisor_eq_point : meromorphicMap.poles = Divisor.point P

/-- **Riemann-Roch leaf.** On a compact connected genus-zero Riemann surface,
for every point `P` there is a meromorphic function with exactly one simple
pole at `P`.

Bottom-up content: prove the Riemann-Roch calculation `ℓ(P) = 2`, choose a
nonconstant element of `L(P)`, and identify its pole divisor as `[P]`. -/
theorem genusZero_fixedPole_meromorphicData_nonempty
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (P : X)
    (h : analyticGenus ℂ X = 0) :
    Nonempty (GenusZeroFixedPoleMeromorphicData X P h) := by
  sorry

end JacobianChallenge.HolomorphicForms
