# R1 — Radó's triangulation theorem

**Headline.** Every compact connected oriented topological 2-manifold
admits a finite triangulation: a homeomorphism with the underlying
space of a finite abstract simplicial 2-complex.

**Lean target.** `JacobianChallenge.Analysis.Rado.rado_overview`
in `Overview.lean`; full realisation will replace
`StageA.rado_triangulation_theorem`.

**Build.** `lake build Jacobian.Analysis.Rado`

## Classical proof (4 phases)

1. **Finite chart cover.** Compactness gives finitely many disk
   charts.
2. **PL approximation.** Doyle–Moran: dim-2 homeomorphisms of open
   subsets of `ℝ²` are uniformly PL-approximable.  Adjust
   compatibly across the atlas.
3. **Simplicial-complex assembly.** Triangulate each PL chart; take
   common subdivisions across overlaps.
4. **Manifold link verification + homeomorphism promotion.** Verify
   2-manifold conditions; glue chart maps; compact + T2 ⇒
   homeomorphism.

This is the dimension-2-specific argument — it fails in dimension
≥ 5 (Kirby–Siebenmann).

## Lean plan (sub-leaves under `Overview.lean`)

| Sub-leaf | Phase | Status | Notes |
|---|---|---|---|
| `rado_finite_disk_atlas` | 1 | DONE in `StageA/RadoTheorem.lean` | Uses `IsCompact.elim_finite_subcover` |
| `rado_pre_disk_refinement` | 1 | placeholder | Lebesgue-number argument |
| `rado_dim2_local_pl_approx` | 2 | placeholder | Doyle–Moran |
| `rado_dim2_pl_approx_uniform` | 2 | placeholder | Compact-open closeness |
| `rado_pl_cocycle_preservation` | 2 | placeholder | Per-overlap induction |
| `rado_pl_atlas_finite_induction` | 2 | placeholder | Atlas-level induction |
| `rado_triangulate_each_chart` | 3 | placeholder | Disk subdivision |
| `rado_common_subdivision_overlaps` | 3 | placeholder | Cross-overlap refinement |
| `rado_assembled_edges_in_two_triangles` | 3 | placeholder | 2-manifold edge condition |
| `rado_assembled_vertex_link_is_circle` | 3 | placeholder | 2-manifold vertex condition |
| `rado_chart_homeo_glues_continuous` | 4 | placeholder | Chart-by-chart continuity |
| `rado_chart_homeo_glues_bijective` | 4 | placeholder | Inverse function |
| `rado_compact_to_T2_promote` | 4 | placeholder | Mathlib `Continuous.homeoOfEquivCompactToT2` |

## Recursive sub-gaps

* **R1-sub-A.** Abstract simplicial complexes + geometric realisation
  with colimit topology.  Mathlib has none; sketched at
  `Jacobian/StageA/SimplicialComplex.lean`.  ~400 LOC.
* **R1-sub-B.** Schoenflies-type theorem in dimension 2 for PL
  approximation.  ~250 LOC.
* **R1-sub-C.** `IsCombinatorial2Manifold` predicate.  ~30 LOC for
  the definition; example verification depends on Phase 3.

## Plain-English

Radó's theorem says every compact 2-dimensional surface can be cut
into a finite collection of triangles glued along edges.  The proof
covers the surface with disks, smooths chart overlaps to piecewise
linear, fits the PL pieces into a simplicial complex, and verifies
the result is a 2-manifold.  The PL step works only in dimension
≤ 3.  Without Radó, the polygonal-model chain has no input.

## See also

* Blueprint section `subsec:gap-R1-rado` in
  `tex/sections/12-classical-analysis-gaps.tex`.
* Bottom-up sketch `Jacobian/StageA/RadoTheorem.lean` (~150 LOC of
  typed sorries).
* Original source: T. Radó, *Über den Begriff der Riemannschen
  Fläche* (1925); Doyle–Moran (1968); Thomassen (1992).

**Estimated full LOC** (R1 + sub-A + sub-B + sub-C): 2000–2700.
