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
