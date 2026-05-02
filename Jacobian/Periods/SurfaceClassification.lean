import Jacobian.Periods.Polygon4g
import Jacobian.Periods.Orientable
import Jacobian.Periods.TopologicalGenus
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Stage A umbrella: surface classification

This file states the **Stage A** obligation of `ref/plans/polygonal-model.md`:
every compact connected orientable smooth real 2-manifold `M` is
homeomorphic to the standard fundamental polygon `Polygon4g`
of its topological genus.

## Top-down role

`compactOrientableSurface_homeomorph_polygon4g_topologicalGenus`
is the named obligation that the umbrella `polygonal_model`
delegates to. It carries the bulk of the classical-topology work
(Radó's triangulation theorem, combinatorial reduction to the
standard `4g`-gon edge word, identification of that quotient with
`Polygon4g g`).

## Bottom-up content

A canonical Lean discharge would proceed via:

* `compact_2manifold_admits_triangulation` (Radó),
* `triangulated_orientable_surface_word` (combinatorial reduction to the
  standard `a₁b₁a₁⁻¹b₁⁻¹⋯` edge word),
* `polygon_word_to_quotient` (identification with `Polygon4g g`),
* a final assembly producing the homeomorphism for the unique `g'`
  that arises, which by uniqueness of singular homology equals
  `topologicalGenus M`.

Each leaf is itself a multi-hundred-LOC project; see
`ref/plans/polygonal-model.md` Stage A and the future
`ref/plans/surface-classification.md` for the next-level decomposition.
-/

namespace JacobianChallenge.Periods

open scoped Manifold

/-- **Stage A umbrella (surface classification).** A compact connected
orientable smooth real 2-manifold `M` is homeomorphic to the standard
fundamental polygon `Polygon4g (topologicalGenus M)`.

This is the polygonal-model statement *with the topology already
expressed as the topological genus*, so its hypothesis side is purely
real-2-manifold and its target genus is the topologically-defined one.
The complex-vs-topological genus comparison is handled separately by
`analyticGenus_eq_topologicalGenus` and is not a job of Stage A. -/
theorem compactOrientableSurface_homeomorph_polygon4g_topologicalGenus
    (M : Type) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    [Orientable M] :
    Nonempty (M ≃ₜ Polygon4g (topologicalGenus M)) := by
  sorry

end JacobianChallenge.Periods
