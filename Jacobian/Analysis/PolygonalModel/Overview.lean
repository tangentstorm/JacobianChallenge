/-!
# R3 — The polygonal-model theorem

Headline statement:

> A compact connected oriented Riemann surface `X` of analytic genus
> `g` is homeomorphic to the standard fundamental polygon
> `Polygon4g(g) := overline(D¹) / ~_side`, the closed unit disk
> quotiented by the side-pairing
> `a₁ b₁ a₁⁻¹ b₁⁻¹ ⋯ a_g b_g a_g⁻¹ b_g⁻¹`.

R3 is the umbrella that *consumes* R1 (Radó) and R2 (Tietze) and
*produces* the homeomorphism `X ≅ Polygon4g(g)` used by every
period-lattice argument downstream.

Pre-existing scaffolding:
* `Jacobian/Periods/Polygon4g*.lean` (the polygon side, sorry-free).
* `Jacobian/Periods/SurfaceClassification.lean`,
  `TietzeReduction.lean`, `Polygon4gCellular.lean`,
  `H1EvenBasisViaSurfaceClassification.lean` (project-side
  decomposition; some sorry-free, some sorry).
* `Jacobian/StageA/{SimplicialComplex,RadoTheorem,SpanningTree,
  PrismOperator,Hurewicz,EdgeWordTietze,CellularSingular}.lean`
  (bottom-up sketch).

**Status.** Every theorem here is a `True` placeholder; the
realisation `JacobianChallenge.Blueprint.polygonal_model` remains
`sorry`.
-/

namespace JacobianChallenge.Analysis.PolygonalModel

/-! ### Headline -/

/-- **R3 headline (placeholder type).**  `X ≅ₕ Polygon4g(g)` for a
compact connected oriented Riemann surface of analytic genus `g`. -/
theorem polygonal_model_overview : True := trivial

/-! ### Sub-leaves — Phase 1: from Riemann surface to triangulation -/

/-- **R3.1.1.** A compact connected oriented Riemann surface is a
compact connected oriented topological 2-manifold (forget complex
structure, take real charts). -/
theorem polygonal_model_real2_structure : True := trivial

/-- **R3.1.2.** Apply Radó (R1) to obtain a finite triangulation. -/
theorem polygonal_model_apply_rado : True := trivial

/-! ### Sub-leaves — Phase 2: cut along a spanning tree -/

/-- **R3.2.1.** Existence of a spanning tree on the 1-skeleton of any
finite connected combinatorial 2-manifold (Mathlib has
`SimpleGraph.IsTree`; existence theorem missing). -/
theorem polygonal_model_spanning_tree_exists : True := trivial

/-- **R3.2.2.** Cutting along a spanning tree converts the
triangulation's geometric realisation into a polygonal disk
(combinatorially: removing tree edges from the dual graph leaves a
single 2-cell whose boundary is a closed walk). -/
theorem polygonal_model_cut_along_tree : True := trivial

/-- **R3.2.3.** The boundary walk reads off as an edge word of length
`2 · #(non-tree edges)` in a four-letter alphabet labelled by
non-tree edges and their orientations. -/
theorem polygonal_model_boundary_walk_is_edge_word : True := trivial

/-! ### Sub-leaves — Phase 3: reduce the edge word to standard form -/

/-- **R3.3.1.** Apply R2 (Tietze normal form) to reduce the boundary
edge word to `standardWord(g)`. -/
theorem polygonal_model_apply_tietze : True := trivial

/-- **R3.3.2.** The Tietze reduction lifts to a homeomorphism between
the original cut-open polygon and `Polygon4g(g)` (every Tietze move
corresponds to a homeomorphism of polygons via cut-and-paste). -/
theorem polygonal_model_tietze_to_homeomorph : True := trivial

/-! ### Sub-leaves — Phase 4: descend to the surface -/

/-- **R3.4.1.** Compose the cut-and-paste homeomorphism (R3.3.2) with
the descent through the side-pairing quotient to obtain
`X ≅ₕ Polygon4g(g)`. -/
theorem polygonal_model_descent_to_quotient : True := trivial

/-- **R3.4.2.** The constructed homeomorphism is canonical up to
isotopy (different choices of spanning tree give isotopic results). -/
theorem polygonal_model_isotopy_canonicity : True := trivial

/-! ### Stage B sub-leaves — analytic-vs-topological genus -/

/-- **R3.5.1.** The induced smooth real 2-manifold structure on a
complex curve.  Already discharged sorry-free at
`Jacobian/Periods/ComplexChartedSpaceReal2.lean`. -/
theorem polygonal_model_smooth_real_structure : True := trivial

/-- **R3.5.2.** `H₁(Polygon4g(g), ℤ) ≅ ℤ^{2g}` from the explicit
cellular structure. -/
theorem polygonal_model_h1_polygon4g : True := trivial

/-- **R3.5.3.** Topological invariance of H₁ transports
`H₁(X) ≅ H₁(Polygon4g(g))` once R3 is in hand. -/
theorem polygonal_model_h1_invariance : True := trivial

/-! ### Recursive sub-gaps surfaced

* **R3-sub-A.** Spanning-tree existence on finite connected simple
  graphs (R3.2.1).  Tracked at
  `Jacobian/StageA/SpanningTree.lean`.
* **R3-sub-B.** Dual-graph and cut-along-tree combinatorics
  (R3.2.2 / R3.2.3).  Tracked at
  `Jacobian/Periods/DualGraphCut.lean`.
* **R3-sub-C.** Tietze-move-by-cut-and-paste correspondence (R3.3.2).
  No Mathlib analogue; ~150 LOC of routine geometry. -/

theorem polygonal_model_subgap_spanning_tree : True := trivial
theorem polygonal_model_subgap_dual_graph_cut : True := trivial
theorem polygonal_model_subgap_tietze_cut_paste : True := trivial

end JacobianChallenge.Analysis.PolygonalModel
