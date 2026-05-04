# R3 — The polygonal-model theorem

**Headline.** A compact connected oriented Riemann surface `X` of
analytic genus `g` is homeomorphic to the standard fundamental
`4g`-gon `Polygon4g(g)`.

**Lean target.**
`JacobianChallenge.Analysis.PolygonalModel.polygonal_model_overview`
in `Overview.lean`; full realisation lives at
`Blueprint.polygonal_model`.

**Build.** `lake build Jacobian.Analysis.PolygonalModel`

## Classical proof (7 steps)

1. **Real 2-manifold structure.** A complex 1-manifold is a smooth
   real 2-manifold (already discharged sorry-free).
2. **Apply Radó (R1).** Get a finite triangulation of `X`.
3. **Cut along a spanning tree.** Spanning tree of the 1-skeleton
   exists; cutting non-tree edges yields a topological disk whose
   boundary walk has length `4g` (Euler-formula constraint).
4. **Read off the edge word.** Each non-tree edge ↦ two boundary
   appearances ↦ four-letter alphabet `a_i, b_i, a_i⁻¹, b_i⁻¹`.
5. **Apply Tietze (R2).** Reduce the boundary word to the standard
   relator.
6. **Lift Tietze moves to homeomorphisms.** Each move ↦ cut-and-paste
   homeomorphism of polygons.
7. **Descend to surface.** Both polygons quotient to topologically
   the same surface; homeomorphism descends to `X ≅ Polygon4g(g)`.

## Lean plan (sub-leaves under `Overview.lean`)

| Sub-leaf | Phase | Status |
|---|---|---|
| `polygonal_model_real2_structure` | 1 | DONE (sorry-free) |
| `polygonal_model_apply_rado` | 1 | placeholder; invoke R1 |
| `polygonal_model_spanning_tree_exists` | 2 | placeholder; R3-sub-A |
| `polygonal_model_cut_along_tree` | 2 | placeholder; R3-sub-B |
| `polygonal_model_boundary_walk_is_edge_word` | 2 | placeholder |
| `polygonal_model_apply_tietze` | 3 | placeholder; invoke R2 |
| `polygonal_model_tietze_to_homeomorph` | 3 | placeholder; R3-sub-C |
| `polygonal_model_descent_to_quotient` | 4 | placeholder |
| `polygonal_model_isotopy_canonicity` | 4 | placeholder |
| `polygonal_model_smooth_real_structure` | 5 | DONE (sorry-free) |
| `polygonal_model_h1_polygon4g` | 5 | placeholder |
| `polygonal_model_h1_invariance` | 5 | placeholder |

The polygon side (`Polygon4g`, edge words, side-pairing, Tietze
relation) is already extensively formalized in `Jacobian/Periods/`,
mostly sorry-free.

## Recursive sub-gaps

* **R3-sub-A.** Spanning-tree existence (`SimpleGraph.IsTree`
  exists, existence theorem missing).  ~80 LOC.
* **R3-sub-B.** Dual-graph + cut-along-tree combinatorics.
  ~250 LOC.
* **R3-sub-C.** Tietze-move-to-cut-and-paste correspondence.
  ~400 LOC, careful chart-management; no Mathlib analogue.

## Plain-English

The polygonal model is the bridge between the curved surface and a
flat polygon (square for torus, octagon for genus-2, `4g`-gon for
genus `g`).  Inside the polygon: simply connected, flat, Stokes-friendly.
On the boundary: the entire topological complexity, encoded in the
gluing pattern.  R3 produces the homeomorphism: triangulate (R1),
cut along a spanning tree, simplify the boundary word (R2), lift
moves to cut-and-paste homeomorphisms.  Once it lands, the rest of
the period-lattice chain (Stokes on the polygon, Riemann bilinear,
period fullness) becomes accessible.

## See also

* Blueprint section `subsec:gap-R3-polygonal-model` in
  `tex/sections/12-classical-analysis-gaps.tex`.
* Existing project-side scaffolding under `Jacobian/Periods/` and
  `Jacobian/StageA/`.
* Plan: `ref/plans/polygonal-model.md`.

**Estimated full LOC** (R3 + sub-A + sub-B + sub-C): 1500–2000.
