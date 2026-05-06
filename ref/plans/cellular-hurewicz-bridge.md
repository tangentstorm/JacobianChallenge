# Bridge to Mathlib: closure plan for cellular Hurewicz

Path from the current branch state (12 commits, 6 named sub-sorries
on the cellular path) to a fully sorry-free `polygon4g_succ_singularH1_hurewiczIso`.

This plan separates the work into **in-project** items (provable
inside this repository against Mathlib v4.28.0 as it stands) and
**upstream-Mathlib** items (require new Mathlib lemmas to be added,
either here as project-local lemmas or as upstream PRs).

## Current sorry inventory

| # | Sorry | File | Mathlib gap | Strictly weaker than iso? |
|---|-------|------|-------------|---------------------------|
| 1 | `polygon4g_succ_singularH1_isFinite` | Polygon4gCellular | None — derivable from edge basis | ✓ |
| 2 | `polygon4g_succ_singularH1_isTorsionFree` | Polygon4gCellular | None — derivable from edge basis | ✓ |
| 3 | `polygon4g_succ_singularH1_finrank_eq` | Polygon4gCellular | None — derivable from edge basis | ✓ |
| 4 | `singularChainElement_boundary_decomposition` | SingularChainElement | None — categorical bookkeeping | ✓ |
| 5 | `edgeBasisMap_injective` | Polygon4gEdgeBasisMap | None — chain-coefficient extraction | ✓ |
| 6 | `edgeBasisMap_surjective` | Polygon4gEdgeBasisMap | **Major** — subdivision API | ✓ |

Sorries 1-3 have a parallel cellular discharge (already wired
through `polygon4g_succ_singularH1_hurewiczIso_via_edgeBasis`) once
sorries 4-6 land. So the **effective gap is just 4-6**.

## Stage A — In-project, no upstream Mathlib needed

Each item below is provable in this repository against Mathlib
v4.28.0 as it stands. They form the "easy half" of the closure.

### A1. Boundary decomposition (sorry #4)

**Status:** Typed equation in
`SingularChainElement.lean#singularChainElement_boundary_decomposition`,
sorry'd proof. The naturality lemma `sigmaConst_obj_map_ι` is
sorry-free.

**Mathlib ingredients (all present):**
* `alternatingFaceMapComplex_obj_d` — gives `K.d (n+1) n = ∑ (-1)^i • δ_i`.
* `Sigma.ι_comp_map'` — naturality of coproduct injection under
  `Sigma.map'`.
* `LinearMap.map_sum`, `LinearMap.map_smul` — additive/linear
  computations.
* `ConcreteCategory` instance for `ModuleCat ℤ`.

**Proof outline (50-100 lines):**
1. Unfold `K.d (n+1) n` via `alternatingFaceMapComplex_obj_d` to
   `∑_{i : Fin (n+2)} (-1)^i • M.δ i` where M is the simplicial
   object.
2. Identify `M.δ i = (sigmaConst.obj R).map (K_set.δ i)` via the
   functor composition unfolding.
3. Apply `sigmaConst_obj_map_ι` (already sorry-free) to commute
   `Sigma.ι _ s ≫ M.δ i = Sigma.ι _ (K_set.δ i s)`.
4. Apply both sides to `(1 : ℤ)`.
5. Identify `K_set.δ i s` with `singularSimplexFace σ i` via
   `TopCat.toSSetObjEquiv` naturality.
6. Sum with alternating signs.

**Cost:** ~50-100 lines, focused 1-2 days.

### A2. `edgeChain_isCycle` (Phase 3 cycle property)

**Status:** Currently a `True` placeholder in
`Polygon4gEdgeChain.lean`. Becomes a real cycle equation given A1.

**Mathlib ingredients:** A1 + `edgeSimplex_faces_eq` (sorry-free,
already in this branch).

**Proof outline:** Apply A1 with `n = 0`, use `Fin.sum_univ_two`
to expand `∑_{i : Fin 2} ...` as `term_0 - term_1`, then
`edgeSimplex_faces_eq` makes the two terms equal so the difference
is zero.

**Cost:** ~20 lines, half a day.

### A3. Homology projection wiring (Phase 4 leaf)

**Status:** `edgeHomologyClass` is `0` placeholder. Needs the real
projection from cycles to homology.

**Mathlib ingredients (all present):**
* `HomologicalComplex.cyclesMk` — constructs a cycle from a chain
  with `d c = 0`. Available via `Mathlib.Algebra.Homology.ConcreteCategory`.
* `HomologicalComplex.homologyπ` — projection from cycles to
  homology (in `HomologicalComplex.HomologySequence`).
* The composition gives the homology class.

**Proof outline:** Apply `K.cyclesMk (edgeChain g i) 0 rfl
edgeChain_isCycle` to get a cycle, then push through
`homologyπ`. The result lives in `singularH1` (= `K.homology 1`).

**Cost:** ~30 lines, half a day. Needs A2 (which needs A1).

### A4. `edgeBasisMap_injective` (sorry #5, Phase 6.a)

**Status:** Sorry'd. Becomes potentially provable once A3 lands.

**Mathlib ingredients:**
* `Sigma.desc` — produces a "coefficient extraction" linear map
  for each generator.
* `LinearMap.ker_eq_bot` — characterisation of injectivity.
* The chain-coefficient route: each simplex has a "dual" projection
  `coeff_σ : C_n → ℤ` given by `Sigma.desc` with `1` at index σ
  and `0` elsewhere.

**Proof outline:**
1. For each `i : Fin (2*(g+1))`, build a chain-level coefficient
   functional `coeffEdge i : SingularChain (Polygon4g (g+1)) 1 →ₗ[ℤ] ℤ`
   that is `1` on `edgeChain g i` and `0` on all other simplices.
2. Show `coeffEdge i` factors through cycles (it's already defined
   on the chain group).
3. Show it descends to homology (the boundary subgroup pairs to 0
   with `coeffEdge i` because boundaries are 2-cell faces, none of
   which equal an edge simplex).
4. Combined: a linear functional `homCoeff i : singularH1 (Polygon4g (g+1)) →ₗ[ℤ] ℤ`
   with `homCoeff i (edgeHomologyClass g j) = δ_{i,j}`.
5. This forces the edge homology classes to be linearly independent
   (any nontrivial linear combination has non-zero coefficient
   under one of the `homCoeff i`).

**Cost:** ~150-200 lines, 2-4 days. The most subtle step is (3) —
showing that boundaries (= 2-cell relator faces) pair to 0 with
`coeffEdge i`.

**Note:** Step (3) itself uses the polygon-specific structure: the
2-cell of `Polygon4g (g+1)` has boundary equal to the polygon
relator, which is a sum of commutators, hence its `coeffEdge i`
projection is zero (using
`commutator_product_abelianizes_to_zero` already proved in
`Polygon4gCellular.lean`).

### A5. `polygon4g_succ_singularH1_isTorsionFree` (sorry #2)

**Status:** Sorry'd in `Polygon4gCellular.lean`. Becomes derivable
once A4 lands (combined with surjectivity from B1 below):
* `edgeBasisMap` injective (A4) + `edgeBasisMap` surjective (B1) →
  `edgeBasisMap` is an iso → `singularH1` is iso to `Fin (2*(g+1)) → ℤ`,
  which is torsion-free.

**Cost:** ~10 lines, trivial given A4 + B1.

## Stage B — Major in-project work, no Mathlib upstream

### B1. `edgeBasisMap_surjective` (sorry #6, Phase 6.b)

**Status:** Sorry'd. The hardest remaining piece.

**Mathlib gap:** No subdivision API for singular chains.

**Required new Mathlib-level infrastructure (would-be upstream PRs):**

* **B1.a `singularChainBarycentricSubdivision`** — a chain map
  `S : C_n(X) → C_n(X)` plus a chain homotopy `H : S ≃ id` showing
  every cycle is homologous to its barycentric subdivision.
  Iterated subdivision can shrink simplices to fit inside an open
  cover. Estimated 500-800 lines of Mathlib infrastructure.

* **B1.b `singularChain_smallSimplices`** — Lebesgue-covering /
  small-simplices theorem: for any open cover of `X`, every cycle
  is homologous to one whose simplices each lie in some open of
  the cover. Direct corollary of B1.a + iteration. Estimated
  100-200 lines.

* **B1.c `excision_polygon_to_skeleton`** — the polygon-specific
  application: for the standard `Polygon4g (g+1)` open cover with
  one open per face (interior of 2-cell + thickened 1-skeleton +
  vertex neighbourhoods), every cycle is homologous to one
  supported on the 1-skeleton. Estimated 200 lines.

**Polygon-specific shortcut (alternative to general subdivision):**

The polygonal model's combinatorial structure may admit a more
direct argument, bypassing general subdivision:

* Use the surjectivity of `Polygon4g.mk : DiskC → Polygon4g (g+1)`
  to lift singular cycles in `Polygon4g (g+1)` to the disk.
* Singular `H₁` of the disk is zero (it's contractible), so every
  cycle in `Polygon4g (g+1)` lifts to a chain in the disk whose
  boundary is supported on the side-pairing relations.
* The boundary structure forces the cycle in `Polygon4g (g+1)` to
  be a sum of edge classes modulo the relator.

**Cost (polygon-specific shortcut):** ~300-500 lines, 1-2 weeks.

**Cost (general subdivision API):** ~800-1200 lines, 3-4 weeks.

### B2. `polygon4g_succ_singularH1_isFinite` (sorry #1)

**Status:** Sorry'd. Once B1 lands and `edgeBasisMap` is surjective,
follows from `Module.Finite.of_surjective` (already wired through
`polygon4g_succ_singularH1_isFinite_via_edgeBasisMap`).

**Cost:** ~5 lines, trivial given B1.

### B3. `polygon4g_succ_singularH1_finrank_eq` (sorry #3)

**Status:** Sorry'd. Once A4 + B1 land and `edgeBasisMap` is bijective,
follows from `Module.Basis.mk` + `finrank_eq_card_basis`.

**Cost:** ~10 lines, trivial given A4 + B1.

## Stage C — Optional Mathlib upstream contributions

These are not strictly needed for closure (the project-local
lemmas suffice), but if landed in Mathlib, they would be cleaner
foundations:

### C1. Hurewicz theorem (general form)

`Hurewicz.{0} X : H₁(X, ℤ) ≅ π₁(X)^{ab}` for path-connected `X`.

* Requires the prism construction (already partially scaffolded
  in `Jacobian.Periods.SingularH1Homotopy`).
* Requires identifying `π₁` with the FundamentalGroupoid's
  endomorphism group at a basepoint.
* Estimated 500-1000 lines for upstream Mathlib PR.

### C2. Surface group presentation

`SurfaceGroup g := ⟨a₀, b₀, …, a_g, b_g | ∏ᵢ [aᵢ, bᵢ]⟩` as a
`Group` instance, with the universal property giving its
fundamental group identification for closed orientable surfaces.

* Requires Seifert-van Kampen for the polygon decomposition.
* Estimated 300-500 lines.

### C3. CW-complex structure

A CW-complex API with cellular chain complex, cellular homology
agreeing with singular homology, etc.

* Major gap in Mathlib v4.28.0.
* Estimated 2000-3000 lines for full development.

## Recommended order of attack

1. **A1** — Boundary decomposition (sorry #4). Unblocks A2-A5 + B1-B3.
2. **A2** — `edgeChain_isCycle`. Trivial given A1.
3. **A3** — Homology projection. Unblocks A4-A5 + B1-B3.
4. **A4** — Linear independence (sorry #5). Unblocks A5 + B3.
5. **B1** — Spanning (sorry #6). The big one. Use polygon-specific
   shortcut (lift to disk).
6. **A5, B2, B3** — derived sorries (1-3) become immediate.

**Total estimated cost** for full closure: ~1000-1700 lines, 4-6
weeks of focused work. The bulk (~70%) is B1.

If only Stage A lands, sorries #4 and #5 become discharged, leaving
only `edgeBasisMap_surjective` (sorry #6) as the single residual
named leaf — exactly the "permitted single sub-sorry" the original
task instructions allowed.

## Stage A first session (this session): seed work

Of Stage A, the items achievable in a single focused session are:

* **A1 sketch** — write the boundary decomposition proof carefully,
  even if it doesn't fully close, the framework lands.
* **A2** — `edgeChain_isCycle` real equation.
* **A3** — homology projection wiring (Mathlib API exploration +
  basic plumbing).

Items A4 and B1 require substantial focused work that doesn't fit
in a single session.
