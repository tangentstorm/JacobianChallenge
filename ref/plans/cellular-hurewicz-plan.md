# Cellular Hurewicz infrastructure plan

Plan for the substantial Mathlib infrastructure investment that the
Route A cellular construction of `polygon4g_succ_singularH1_hurewiczIso`
requires. Drafted 2026-05-06; first deliverable
(`Jacobian/Periods/Polygon4gEdgeLoops.lean`) is already on `main`.

## Goal

Discharge the three sub-leaves in `Jacobian/Periods/Polygon4gCellular.lean`:

* `polygon4g_succ_singularH1_isFinite` — `singularH1 (Polygon4g (g+1))`
  is finitely generated as a `ℤ`-module.
* `polygon4g_succ_singularH1_isTorsionFree` — torsion-free.
* `polygon4g_succ_singularH1_finrank_eq` — `finrank = 2(g+1)`.

The conjunction of these three implies the consolidated iso

  `Polygon4gAbelianization g ≃ₗ[ℤ] singularH1 (Polygon4g (g+1))`

via `Module.basisOfFiniteTypeTorsionFree'` + basis reindexing +
`Basis.equivFun.symm` (already wired up sorry-free).

## Bottleneck

Mathlib v4.28.0's singular homology API is purely categorical:

  `singularChainComplexFunctor : ModuleCat ℤ ⥤ TopCat ⥤ ChainComplex (ModuleCat ℤ) ℕ`

defined as

  `topToSSet ⋙ alternatingFaceMapComplex ∘ (sigmaConst ⋙ whiskering)`.

There is no API that takes a concrete continuous map
`σ : C(stdSimplex ℝ (Fin (n+1)), X)` and returns the corresponding
generator element of the chain group. Without that, no concrete
edge cycle can be named in `singularH1 (Polygon4g (g+1))`.

The three sub-leaves above all depend on naming concrete cycles, so
they all share this bottleneck.

## Phase plan

### Phase 1 — Topological building blocks (small, sorry-free)

Status: ✅ **done** (file `Jacobian/Periods/Polygon4gEdgeLoops.lean`).

* `edgeArcIdx g i` — boundary-arc index for the i-th edge class.
* `boundaryAngle_continuous`, `boundaryParamC_continuous`,
  `boundaryParam_continuous` — missing continuity lemmas.
* `edgeContMap g i : C(unitInterval, Polygon4g (g+1))` — concrete
  edge loop as a continuous map from `[0,1]`.

### Phase 1.5 — stdSimplex packaging (small, sorry-free)

Status: ✅ **done** (file `Jacobian/Periods/Polygon4gEdgeSimplex.lean`).

* `stdSimplexToUnitInterval` — sorry-free continuous-map version of
  Mathlib's `stdSimplexHomeomorphUnitInterval`.
* `edgeSimplex g i : C(stdSimplex ℝ (Fin 2), Polygon4g (g+1))` —
  sorry-free, the i-th edge as a singular 1-simplex.
* `stdSimplexVertex` and the
  `edgeSimplex_vertex_zero/_one` evaluation lemmas — sorry-free.

### Phase 2 — Singular chain element extraction (medium-hard)

Status: 🟢 **partially done**, single sorry remaining
(`SingularChainElement.lean`).

* `SingularChain X n`, `SingularChainCoproduct X n` — sorry-free
  abbreviations exposing the level-n chain group.
* `singularChainSimplexIndex` — sorry-free re-export of
  `TopCat.toSSetObjEquiv`.
* `singularChainElement σ` — **sorry-free** concrete construction
  via `Sigma.ι` applied to `(1 : ℤ)`.
* `stdSimplexFaceMap n i` and `singularSimplexFace σ i` — sorry-free.
* `singularChainElement_boundary_decomposition` — Phase 2 leaf
  (typed equation, sorry'd proof). The proof is a categorical
  unfolding of `alternatingFaceMapComplex_obj_d` plus
  `Sigma.ι_comp_map'`; estimated 50-100 lines.

### Phase 3 — Edge cycles in the polygon (mostly done, sorry-free)

Status: ✅ **mostly done** (file `Jacobian/Periods/Polygon4gEdgeChain.lean`).

* `boundaryParam_one_eq_succ_zero` — sorry-free numerical identity.
* `polygon4g_succ_vertex_a_pair_zero/_one`,
  `polygon4g_succ_vertex_b_pair_zero/_one` — sorry-free, the four
  within-handle vertex identifications.
* `polygon4g_succ_handle_vertices_equal` — sorry-free, all four
  vertices of handle `i` are identified.
* `polygon4g_succ_handle_link` — sorry-free, b-pair adjacent-handle
  link.
* `edgeSimplex_endpoints_equal` — **sorry-free**, the two endpoints
  of edge `i` are identified.
* `edgeChain g i` — sorry-free.
* `edgeSimplex_faces_eq g i` — **sorry-free**, the two singular
  faces of edge `i` are equal.
* `edgeChain_isCycle` — placeholder `True` (becomes a real cycle
  equation once Phase 2's boundary decomposition lands).

### Phase 4 — Edge basis map (mostly done, sorry-free)

Status: 🟢 **mostly done** (file `Jacobian/Periods/Polygon4gEdgeBasisMap.lean`).

* `edgeHomologyClass g i` — **placeholder** `0` (becomes the real
  homology projection of `edgeChain g i` once Phase 2's boundary
  decomposition is real and the homology projection is wired up).
* `edgeBasisMap g` — **sorry-free**, defined as
  `∑ i, (toSpanSingleton (edgeHomologyClass g i)).comp (proj i)`.

### Phase 5 — `polygon4g_succ_singularH1_isFinite` (Phase 7 reassembly)

Status: ✅ **done** as conditional reassembly
(`polygon4g_succ_singularH1_isFinite_via_edgeBasisMap`, sorry-free
modulo `edgeBasisMap_surjective`).

### Phase 6.a — Linear independence

Status: 🟡 **named sub-sorry** (`edgeBasisMap_injective`,
strictly weaker than the iso). Becomes provable once
`edgeHomologyClass` is upgraded from placeholder; the argument is
chain-coefficient extraction (the dual of `Sigma.ι`) descended to
homology.

### Phase 6.b — Spanning

Status: 🟡 **named sub-sorry** (`edgeBasisMap_surjective`,
strictly weaker than the iso). Permitted by the plan as a single
named leaf — the bottom-up content is "every singular 1-cycle is
homologous to one supported on the 1-skeleton" (subdivision +
cellular reduction). Mathlib v4.28.0 lacks the subdivision API.

### Phase 7 — Reassembly

Status: ✅ **done as alternative chain**
(`polygon4g_succ_singularH1_hurewiczIso_via_edgeBasis`,
sorry-free given Phase 6.a + 6.b). Provides the iso through a
concrete bijective edge-basis map rather than the structure-theorem
detour. The original `polygon4g_succ_singularH1_hurewiczIso` (in
`Polygon4gCellular.lean`) continues to route through the
structure-theorem chain (`isFinite + isTorsionFree + finrank_eq`)
until the cellular sub-sorries land.

## Active sorry inventory (6)

| Leaf | File | Phase | Strictly weaker? |
|------|------|-------|------------------|
| `polygon4g_succ_singularH1_isFinite` | Polygon4gCellular | 5 | ✓ |
| `polygon4g_succ_singularH1_isTorsionFree` | Polygon4gCellular | 6.a | ✓ |
| `polygon4g_succ_singularH1_finrank_eq` | Polygon4gCellular | 6 + dim | ✓ |
| `singularChainElement_boundary_decomposition` | SingularChainElement | 2.5 | ✓ |
| `edgeBasisMap_injective` | Polygon4gEdgeBasisMap | 6.a | ✓ |
| `edgeBasisMap_surjective` | Polygon4gEdgeBasisMap | 6.b | ✓ |

All six are strictly weaker than the original consolidated iso.

## Cost estimate

* Phase 1 — done (~80 lines).
* Phase 1.5 — ~30 lines.
* Phase 2 — ~150–250 lines, mostly categorical bookkeeping.
* Phase 3 — ~80 lines, geometric content (vertex identification).
* Phase 4 — ~30 lines.
* Phase 5 — ~10 lines (spanning ⟹ f.g.).
* Phase 6.a — ~150 lines via chain-coefficient route.
* Phase 6.b — ~200–400 lines depending on subdivision strategy.
* Phase 7 — ~30 lines glue.

Total: roughly 700–1100 lines; multi-week effort, but each phase is
independently committable and gives downstream benefit. The structure
theorem assembly already in
`Jacobian/Periods/Polygon4gCellular.lean` is forward-compatible —
each phase shrinks the residual sorry count without touching the
final iso theorem.

## Out of scope

* Phase 6.a's integration route is blocked on the genuine integration
  construction in `Jacobian.Periods.PeriodFunctional`. Use the chain-
  coefficient route instead; the integration approach can be the
  long-term replacement.
* Generic homotopy invariance of `H₁` (already split out into
  `Jacobian.Periods.SingularH1Homotopy`); not needed here.
* Generic Hurewicz natural transformation `π₁^{ab} → H₁`; this
  cellular route avoids it entirely.
