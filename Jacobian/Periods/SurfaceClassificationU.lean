import Jacobian.HolomorphicForms.CompactRiemannSurface
import Jacobian.Periods.SurfaceClassification
import Jacobian.Periods.IntegralOneCycleU

/-!
# Universe-polymorphic Surface Classification

This file introduces the universe-`u` homeomorphism bridging a compact
connected Riemann surface in `Type u` to the standard `Type 0` fundamental
polygon `Polygon4g`. It serves as the first transport leaf needed to
decompose the `singularH1U_iso_freeZ_of_compact_riemann_surface` provider.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms
open scoped Manifold

universe u

/--
**Provider (Universe-`u` classification homeomorphism).**
A compact connected Riemann surface in `Type u` is homeomorphic to the
`ULift` of the standard fundamental polygon of its analytic genus.

This is a tracked layer-frontier sorry. Its discharge will require
transporting the Type-0 `compactOrientableSurface_homeomorph_polygon4g_topologicalGenus`
to `Type u` via `ULift` and reconciling `analyticGenus ℂ X` with `topologicalGenus`.
-/
theorem compactRiemannSurface_homeomorph_ulift_polygon4g
    (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [FiniteDimensionalHolomorphicOneForms ℂ X] :
    Nonempty (X ≃ₜ ULift.{u} (Polygon4g (analyticGenus ℂ X))) :=
  sorry

/--
**Provider (Universe-`u` Polygonal Cellular H₁ Basis).**
The `IntegralOneCycleU` homology of the lifted fundamental polygon is linearly
isomorphic to `Fin (2 * g) → ℤ`.

This is a tracked layer-frontier sorry. Its discharge requires coefficient
and universe transport from the Type-0 `polygon4g_singularH1_iso_freeZ`.
-/
theorem polygon4g_singularH1U_iso_freeZ (g : ℕ) :
    Nonempty (IntegralOneCycleU (ULift.{u} (Polygon4g g)) ≃ₗ[ℤ] (Fin (2 * g) → ℤ)) :=
  sorry

end JacobianChallenge.Periods
