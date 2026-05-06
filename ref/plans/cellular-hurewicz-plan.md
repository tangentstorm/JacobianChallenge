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

Status: ✅ done (file `Jacobian/Periods/Polygon4gEdgeLoops.lean`).

* `edgeArcIdx g i` — boundary-arc index for the i-th edge class.
* `boundaryAngle_continuous`, `boundaryParamC_continuous`,
  `boundaryParam_continuous` — missing continuity lemmas.
* `edgeContMap g i : C(unitInterval, Polygon4g (g+1))` — concrete
  edge loop as a continuous map from `[0,1]`.

### Phase 1.5 — stdSimplex packaging (small, sorry-free)

Status: ⏳ planned (this PR).

* Recognise that Mathlib already provides
  `stdSimplexHomeomorphUnitInterval : stdSimplex ℝ (Fin 2) ≃ₜ unitInterval`
  (`Mathlib.Analysis.Convex.StdSimplex`).
* Define
  `edgeSimplex g i : C(stdSimplex ℝ (Fin 2), Polygon4g (g+1))` as
  `edgeContMap g i ∘ stdSimplexHomeomorphUnitInterval.toContinuousMap`.
* Provide `edgeSimplex_zero` / `edgeSimplex_one` evaluation lemmas.

This is the cleanest direct deliverable and gives the chain-extraction
phase its concrete inputs.

### Phase 2 — Singular chain element extraction (medium-hard)

Status: 🚧 hardest single chunk; planned for a follow-up PR.

Goal: a function

  `singularChainElement : C(stdSimplex ℝ (Fin (n+1)), X) →
    ((singularChainComplexFunctor (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)).X n`

that sends a continuous singular n-simplex to its chain-complex
generator. The construction:

1. Use `TopCat.toSSetObjEquiv X ⟨⦋n⦌⟩.symm` to convert `σ` to an
   element of the n-simplices `(toSSet.obj X).obj ⦋n⦌ᵒᵖ`.
2. The chain complex's n-th level is
   `(sigmaConst.obj (ModuleCat.of ℤ ℤ)).obj ((toSSet.obj X).obj ⦋n⦌ᵒᵖ)
     = ∐_{σ} (ModuleCat.of ℤ ℤ)`. Use the coproduct injection
   `Sigma.ι _ σ` to get a morphism `ℤ → ⨁ ℤ`.
3. Apply this morphism to `1 : ℤ` to extract the actual element.

Companion lemmas:
* `singularChainElement_smul`, `singularChainElement_add` — additive
  structure (trivially from coproduct API).
* Boundary identity: `d (singularChainElement σ) = ∑ᵢ (-1)^i •
    singularChainElement (σ ∘ stdSimplex.faceMap i)` where the
  `faceMap i` are the i-th face inclusions
  `stdSimplex (Fin n) → stdSimplex (Fin (n+1))`. The Mathlib `δ_i`
  on the singular simplicial set is exactly precomposition with
  these face maps (after the `toSSetObjEquiv` / `restrictedULiftYoneda`
  unwinding).

### Phase 3 — Edge cycles in the polygon (small given Phase 2)

Status: ⏳ planned.

* `edgeChain g i : ((singularChainComplexFunctor _).obj _).X 1` — the
  chain element of the i-th edge simplex.
* `edgeChain_isCycle g i : d (edgeChain g i) = 0`. Proof: the boundary
  is `(edgeSimplex g i ∘ d_0) - (edgeSimplex g i ∘ d_1)`, two
  zero-simplices = constant maps. Both endpoints map to the same
  identified vertex of the polygon (via the side-pairing identifications
  in `Polygon4g.lean`'s `mk_a_pair` / `mk_b_pair`), so the two
  zero-simplices are equal as elements of the singular simplicial set
  of the polygon, hence cancel.
* `edgeHomologyClass g i : singularH1 (Polygon4g (g+1))` — the
  homology class. Built from the cycle via the canonical projection
  `cycles → homology` in `HomologicalComplex`.

### Phase 4 — `edgeBasisMap` (small)

Status: ⏳ planned.

* `edgeBasisMap g : Polygon4gAbelianization g →ₗ[ℤ] singularH1
    (Polygon4g (g+1))` defined by
  `edgeBasisMap g v := ∑ i, v i • edgeHomologyClass g i`.
* Linearity: free from `Finset.smul_sum` etc.

This converts the abstract `polygon4g_succ_singularH1_finrank_eq`
sub-sorry into the **strictly weaker** companion
`polygon4g_succ_singularH1_finrank_le` (rank ≤ 2(g+1) follows from
spanning by `edgeHomologyClass`) once Phase 6 lands.

### Phase 5 — `polygon4g_succ_singularH1_isFinite` discharged

Status: ⏳ planned, follows from Phase 4.

`Module.Finite ℤ (singularH1 (Polygon4g (g+1)))` follows from the
existence of `edgeBasisMap g` (a surjection onto a f.g. module) plus
spanning (Phase 6.b). Can be discharged directly from
`Submodule.span_eq_top`.

This kills sub-leaf `isFinite`.

### Phase 6 — Bijectivity of `edgeBasisMap` (hard)

Status: ⏳ the big remaining hump after Phase 2.

* **6.a Linear independence (= injectivity).** Build "winding-number"
  ℤ-linear functionals
  `windingNumber g i : singularH1 (Polygon4g (g+1)) →ₗ[ℤ] ℤ`
  satisfying `windingNumber g i (edgeHomologyClass g j) = δᵢⱼ`. Two
  routes:
  - **Integration pairing.** Specialise the pattern in
    `Jacobian.Periods.PeriodFunctional` (`periodPairing`) to a fixed
    holomorphic-form basis dual to the edges. Today this is the zero
    pairing (placeholder), so this route requires the genuine
    integration construction landing too.
  - **Chain-level coefficient extraction.** The chain complex is
    `∐_{σ} ℤ` at level 1; pull out the coefficient of a given σ via
    the dual coproduct projection. Restrict to the cycle subgroup and
    descend to homology. Cleaner; doesn't need integration; but the
    descent needs the boundary structure from Phase 2.

* **6.b Spanning (= surjectivity).** Show `edgeHomologyClass` spans
  `singularH1 (Polygon4g (g+1))`. The classical proof: every singular
  1-cycle is homologous (after barycentric subdivision) to a chain
  supported on the 1-skeleton, and on the 1-skeleton every cycle is
  a sum of edges modulo the 2-cell relator (which is a sum of
  commutators, hence zero in the abelianisation). This step uses
  the classical "small simplices" argument and is the most
  combinatorial.

  If 6.b is intractable in this push, leave it as a single named
  sub-sorry `polygon4g_succ_singularH1_edgeSpanning` — strictly weaker
  than the original iso (it's about a specific spanning family, not
  arbitrary module structure).

### Phase 7 — kill the three Polygon4gCellular leaves

Once 4-6 land:

* `polygon4g_succ_singularH1_isFinite` ← from Phase 5.
* `polygon4g_succ_singularH1_isTorsionFree` ← from `edgeBasisMap`
  injective + image is the whole module (Phase 6.a + 6.b).
* `polygon4g_succ_singularH1_finrank_eq` ← from `edgeBasisMap`
  bijective + `Module.Basis.mk` + `finrank_eq_card_basis`.

All three become sorry-free; the polygonal Hurewicz iso is fully
discharged.

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
