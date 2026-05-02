import Jacobian.Periods.Polygon4g
import Jacobian.Periods.SmoothRealStructure
import Jacobian.Periods.ComplexManifoldOrientable
import Jacobian.Periods.SurfaceClassification
import Jacobian.Periods.AnalyticGenusEqTopologicalGenus
import Jacobian.HolomorphicForms.AnalyticGenus
import Jacobian.HolomorphicForms.FiniteDimensional

/-! # Blueprint stub: `thm:polygonal-model`

Section 3 of `tex/sections/03-periods-and-riemann-bilinear.tex`.

A compact connected oriented Riemann surface `X` of analytic genus `g`
is homeomorphic to a `4g`-gon `P` with sides identified in the
standard pattern `a₁b₁a₁⁻¹b₁⁻¹ ⋯ a_gb_ga_g⁻¹b_g⁻¹`, inducing the
symplectic basis on `H₁`.

## Top-down refinement

The body of `polygonal_model` no longer carries a single monolithic
`sorry`. It is now an *assembly* delegating to four named obligations:

* `JacobianChallenge.Periods.ChartedSpaceComplex_to_smoothReal2`
  (Stage B1, real proof) — induce a smooth real 2-manifold structure
  from the complex 1-manifold structure.
* `JacobianChallenge.Periods.complexManifold_orientable`
  (Stage B2, instance) — register `Orientable X`.
* `JacobianChallenge.Periods.compactOrientableSurface_homeomorph_polygon4g_topologicalGenus`
  (Stage A umbrella, sorry) — surface classification.
* `JacobianChallenge.Periods.analyticGenus_eq_topologicalGenus`
  (Stage B umbrella, sorry) — analytic↔topological genus bridge.

The combinatorial identification of the standard `4g`-gon edge word
with the project-local quotient `Polygon4g g` (constructed in
`Jacobian/Periods/Polygon4g.lean`) is folded into Stage A.

The induced-symplectic-basis half of the blueprint claim is split off
into a separate downstream theorem (deferred until the intersection
form on `H₁(X, ℤ)` lands at the project level).
-/

namespace JacobianChallenge.Blueprint

open JacobianChallenge.Periods JacobianChallenge.HolomorphicForms

open scoped Manifold

/-- **Polygonal model of a compact connected oriented Riemann
surface.** Refined assembly of:

* the complex-to-real smooth structure transport
  (`ChartedSpaceComplex_to_smoothReal2`);
* the orientability of complex manifolds
  (`complexManifold_orientable`);
* surface classification
  (`compactOrientableSurface_homeomorph_polygon4g_topologicalGenus`);
* the analytic–topological genus bridge
  (`analyticGenus_eq_topologicalGenus`). -/
theorem polygonal_model
    (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [FiniteDimensionalHolomorphicOneForms ℂ X]
    (g : ℕ) (_hg : analyticGenus ℂ X = g) :
    Nonempty (X ≃ₜ Polygon4g g) := by
  -- Stage B1: induce smooth real 2-manifold structure on `X`.
  obtain ⟨srStruct⟩ :=
    JacobianChallenge.Periods.ChartedSpaceComplex_to_smoothReal2 X
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) X := srStruct.chartedSpace
  letI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) X := srStruct.isManifold
  -- Stage A: surface classification gives a homeomorphism with `Polygon4g`
  -- of the *topological* genus.
  obtain ⟨homeo⟩ :=
    JacobianChallenge.Periods.compactOrientableSurface_homeomorph_polygon4g_topologicalGenus X
  -- Stage B umbrella: identify topological genus with analytic genus.
  have hbridge :
      analyticGenus ℂ X = JacobianChallenge.Periods.topologicalGenus X :=
    JacobianChallenge.Periods.analyticGenus_eq_topologicalGenus X
  have htg : JacobianChallenge.Periods.topologicalGenus X = g :=
    hbridge.symm.trans _hg
  exact ⟨htg ▸ homeo⟩

end JacobianChallenge.Blueprint
