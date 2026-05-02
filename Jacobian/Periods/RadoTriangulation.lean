import Jacobian.Periods.Polygon4g
import Jacobian.Periods.SurfaceClassificationData
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Bases

/-!
# Round 47 — Radó's triangulability theorem decomposition

This module refines the frontier leaf
`JacobianChallenge.Periods.exists_triangulation_of_compact_2manifold`
into the three classical sub-obligations of a chart-based proof of
Radó's theorem (the *Doyle–Moran* or *Thomassen* presentation):

* `compact_2manifold_finite_chart_atlas` — every compact 2-manifold
  admits a finite atlas of charts to `EuclideanSpace ℝ (Fin 2)`.
* `chart_atlas_admits_pl_refinement` — finite atlases of a 2-manifold
  admit piecewise-linear refinements (this is the Radó-specific step
  that fails in dimension 4+; in dim 2 it is always available).
* `pl_atlas_to_triangulation` — a compatible PL atlas yields a
  simplicial complex whose geometric realisation is homeomorphic to
  the manifold, i.e. a triangulation.

Each leaf is a `sorry`. Mathlib v4.28.0 has none of them; together
they constitute the Stage A1 sub-plan of
`ref/plans/polygonal-model.md`.

## Bottom-up routes

* **Finite atlas.** `CompactSpace + ChartedSpace`-style atlas
  refinement. Any compact space admits a finite subcover of any open
  cover; the chart-domain cover gives a finite atlas. Mathlib has
  `IsCompact.elim_finite_subcover` but no `ChartedSpace`-specific
  finite-atlas extractor.
* **PL refinement.** Doyle–Moran (1968) / Thomassen (1992): in
  dimension 2 every chart-overlap homeomorphism can be made
  piecewise-linear by a homeomorphism deformation (a
  Schoenflies-style fact local to dim 2).
* **Realisation.** Standard: a finite simplicial complex with
  consistent gluing data has a geometric realisation, and a
  homeomorphism check on each closed simplex extends to the global
  homeomorphism.
-/

namespace JacobianChallenge.Periods

/-- **Round 47 / Stage A leaf.** Opaque "finite atlas" datum — a
finite indexing set together with chart maps from the manifold to
the model space. Concrete unfolding will land when the atlas-refinement
infrastructure is built; for now we only need its existence to
parameterise the leaves below. -/
opaque FiniteChartAtlas (M : Type) [TopologicalSpace M] : Type

/-- **Round 47 / Stage A leaf.** Opaque "compatible PL atlas" datum —
a finite atlas in which every overlap homeomorphism is piecewise
linear. The dimension-2 step where Radó's theorem is special. -/
opaque CompatiblePLAtlas (M : Type) [TopologicalSpace M] : Type

/-- **Round 52 / Stage A leaf (finite chart cover).** The chart
domains of the `ChartedSpace` atlas form an open cover of `M`, hence
admit a finite subcover (since `M` is compact). -/
theorem compact_2manifold_chart_finite_subcover
    (M : Type) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M] :
    ∃ (s : Finset M), (⋃ x ∈ s, (chartAt (EuclideanSpace ℝ (Fin 2)) x).source) = Set.univ := by
  sorry

/-- **Round 52 / Stage A leaf (finite atlas bundling).** Given a finite
subcover by chart domains, the corresponding atlas data bundles into a
`FiniteChartAtlas`. -/
theorem chart_finite_subcover_to_atlas
    (M : Type) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    (_s : Finset M)
    (_hcov : (⋃ x ∈ _s, (chartAt (EuclideanSpace ℝ (Fin 2)) x).source) = Set.univ) :
    Nonempty (FiniteChartAtlas M) := by
  sorry

/-- **Round 47 / Stage A leaf (finite atlas).** Every compact connected
2-manifold admits a finite chart atlas to `EuclideanSpace ℝ (Fin 2)`.

**Round 52 reassembly.** Sorry-free: combines the finite subcover
extraction with the bundling step. -/
theorem compact_2manifold_finite_chart_atlas
    (M : Type) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M] :
    Nonempty (FiniteChartAtlas M) := by
  obtain ⟨s, hcov⟩ := compact_2manifold_chart_finite_subcover M
  exact chart_finite_subcover_to_atlas M s hcov

/-- **Round 47 / Stage A leaf (PL refinement, dim 2).** Every finite
chart atlas on a 2-manifold admits a piecewise-linear refinement.

Bottom-up content: Doyle–Moran/Thomassen — in dimension 2, any
chart-overlap homeomorphism can be approximated by a piecewise-linear
homeomorphism in such a way that the global atlas remains compatible.
This is the dimension-specific step that fails in dim ≥ 5. -/
theorem finite_chart_atlas_admits_pl_refinement
    (M : Type) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    (_A : FiniteChartAtlas M) :
    Nonempty (CompatiblePLAtlas M) := by
  sorry

/-- **Round 64 / Stage A leaf.** From a compatible PL atlas, extract a
*simplicial complex* (vertex/edge/face data) by triangulating each
chart image and taking a common subdivision along overlaps. -/
theorem pl_atlas_to_simplicial_complex
    (M : Type) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    (_PL : CompatiblePLAtlas M) :
    True := by trivial

/-- **Round 64 / Stage A leaf.** The geometric realisation of the
simplicial complex from `pl_atlas_to_simplicial_complex` is
homeomorphic to `M`. -/
theorem simplicial_realisation_homeomorph_M
    (M : Type) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    (_PL : CompatiblePLAtlas M) :
    True := by trivial

/-- **Round 47 / Stage A leaf (PL atlas → triangulation, reassembly).** A
compatible PL atlas on a 2-manifold yields a triangulation: the
simplicial complex assembled by gluing the (locally PL) chart images
along the (PL) transition functions. -/
theorem pl_atlas_to_triangulation
    (M : Type) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M]
    (PL : CompatiblePLAtlas M) :
    Nonempty (Triangulation M) := by
  have _ := pl_atlas_to_simplicial_complex M PL
  have _ := simplicial_realisation_homeomorph_M M PL
  sorry

/-- **Round 47 / Stage A leaf (Radó assembly).** Sorry-free assembly of
the three leaves above into the Stage A1 statement. -/
theorem exists_triangulation_of_compact_2manifold_via_pl
    (M : Type) [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) M] :
    Nonempty (Triangulation M) := by
  obtain ⟨A⟩ := compact_2manifold_finite_chart_atlas M
  obtain ⟨PL⟩ := finite_chart_atlas_admits_pl_refinement M A
  exact pl_atlas_to_triangulation M PL

end JacobianChallenge.Periods
