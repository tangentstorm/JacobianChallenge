import Jacobian.Periods.Polygon4g
import Jacobian.Periods.Orientable
import Jacobian.Periods.TopologicalGenus
import Jacobian.Periods.TopologicalGenusInvariance
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
delegates to. It is a 3-leaf assembly:

* `existsHomeoToPolygon4g` — *some* `g' : ℕ` admits `M ≃ₜ Polygon4g g'`.
  This is the heart of the surface-classification theorem: Radó +
  combinatorial reduction + identification with `Polygon4g`.
* `topologicalGenus_polygon4g` — for `g : ℕ`, the polygon `Polygon4g g`
  has topological genus `g`. (Computational; reduces to `H₁` of the
  CW-quotient.)
* `topologicalGenus_homeo_invariant` — `topologicalGenus` is a
  homeomorphism invariant. (Pure Mathlib singular-homology functoriality.)

The umbrella body assembles these: `existsHomeoToPolygon4g` produces
some `g'` and a homeomorphism, then invariance + the polygon
computation pin down `g' = topologicalGenus M`, after which the
homeomorphism is rewritten into the canonical form.

## Bottom-up content

A canonical Lean discharge of `existsHomeoToPolygon4g` would proceed via:

* `compact_2manifold_admits_triangulation` (Radó),
* `triangulated_orientable_surface_word` (combinatorial reduction to the
  standard `a₁b₁a₁⁻¹b₁⁻¹⋯` edge word),
* `polygon_word_to_polygon4g` (identification with `Polygon4g g`).

Each leaf is itself a multi-hundred-LOC project; see
`ref/plans/polygonal-model.md` Stage A and the future
`ref/plans/surface-classification.md` for the next-level decomposition.
-/

namespace JacobianChallenge.Periods

open scoped Manifold

/-- **Stage A1 leaf (existence).** Every compact connected orientable
smooth real 2-manifold is homeomorphic to `Polygon4g g'` for *some*
`g' : ℕ`. Identification of that `g'` with the topological genus is
the Stage A2 leaf. -/
theorem existsHomeoToPolygon4g
    (M : Type) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    [Orientable M] :
    ∃ g' : ℕ, Nonempty (M ≃ₜ Polygon4g g') := by
  sorry

/-- **Stage A2 leaf (polygon genus).** The topological genus of the
standard fundamental polygon `Polygon4g g` equals `g`. Concretely,
`H₁(Polygon4g g, ℤ)` has rank `2g`. -/
theorem topologicalGenus_polygon4g (g : ℕ) :
    topologicalGenus (Polygon4g g) = g := by
  sorry

/-- **Stage A3 leaf (homeomorphism invariance of `topologicalGenus`).**
A topological homeomorphism between compact connected spaces preserves
the topological genus.

Body: by `singularH1_finrank_homeo_invariant`, both sides reduce to the
same `Module.finrank ℤ (singularH1 _)`, then divide by 2. -/
theorem topologicalGenus_homeo_invariant
    {M N : Type} [TopologicalSpace M] [CompactSpace M] [ConnectedSpace M]
    [TopologicalSpace N] [CompactSpace N] [ConnectedSpace N]
    (h : M ≃ₜ N) : topologicalGenus M = topologicalGenus N := by
  unfold topologicalGenus
  rw [singularH1_finrank_homeo_invariant h]

/-- **Stage A umbrella (surface classification).** A compact connected
orientable smooth real 2-manifold `M` is homeomorphic to the standard
fundamental polygon `Polygon4g (topologicalGenus M)`.

Body: assembled from `existsHomeoToPolygon4g`,
`topologicalGenus_polygon4g`, and `topologicalGenus_homeo_invariant`.
The proof has no own `sorry`; all three obligations are named leaves
above. -/
theorem compactOrientableSurface_homeomorph_polygon4g_topologicalGenus
    (M : Type) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    [Orientable M] :
    Nonempty (M ≃ₜ Polygon4g (topologicalGenus M)) := by
  obtain ⟨g', ⟨homeo⟩⟩ := existsHomeoToPolygon4g M
  have hgM : topologicalGenus M = g' := by
    have hinv : topologicalGenus M = topologicalGenus (Polygon4g g') :=
      topologicalGenus_homeo_invariant homeo
    rw [hinv, topologicalGenus_polygon4g]
  exact ⟨hgM ▸ homeo⟩

end JacobianChallenge.Periods
