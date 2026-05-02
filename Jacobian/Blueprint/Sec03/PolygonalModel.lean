import Jacobian.Periods.Polygon4g
import Jacobian.HolomorphicForms.AnalyticGenus
import Jacobian.HolomorphicForms.FiniteDimensional

/-! # Blueprint stub: `thm:polygonal-model`

Section 3 of `tex/sections/03-periods-and-riemann-bilinear.tex`.

A compact connected oriented Riemann surface `X` of genus `g` is
homeomorphic to a `4g`-gon `P` with sides identified in the standard
pattern `a₁b₁a₁⁻¹b₁⁻¹ ⋯ a_gb_ga_g⁻¹b_g⁻¹`, inducing the symplectic
basis on `H₁`.

## Status

Statement-level formalization. The codomain is the project-local
fundamental polygon `JacobianChallenge.Periods.Polygon4g g`
(constructed in `Jacobian/Periods/Polygon4g.lean` as a quotient of
the closed unit disk by side-pairings).

The proof is `sorry`-bound — discharging it is the "surface
classification" project (Radó's triangulation theorem +
combinatorial reduction to the standard 4g-gon, or a Morse-theoretic
handle-decomposition argument). Mathlib v4.28.0 has none of those
classical-topology results as packaged theorems.

The induced-symplectic-basis half of the blueprint claim is split off
into a separate downstream theorem (deferred until the intersection
form on `H₁(X, ℤ)` lands at the project level).
-/

namespace JacobianChallenge.Blueprint

open JacobianChallenge.Periods JacobianChallenge.HolomorphicForms

/-- **Polygonal model of a compact connected oriented Riemann
surface.** Statement-level formalization (proof deferred to surface
classification). -/
theorem polygonal_model
    (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (g : ℕ) (_hg : analyticGenus ℂ X = g) :
    Nonempty (X ≃ₜ Polygon4g g) := by
  sorry

end JacobianChallenge.Blueprint
