import Jacobian.Periods.Polygon4gCellular
import Jacobian.Periods.Polygon4gEdgeChain
import Mathlib.LinearAlgebra.Pi

/-!
# Edge basis map (Phase 4 stub)

Phase 4 of the cellular Hurewicz infrastructure plan
(`ref/plans/cellular-hurewicz-plan.md`).

Goal: assemble the linear map

  `edgeBasisMap g : Polygon4gAbelianization g →ₗ[ℤ] singularH1 (Polygon4g (g+1))`

  `(v : Fin (2*(g+1)) → ℤ) ↦ ∑ i, v i • edgeHomologyClass g i`

where `edgeHomologyClass g i : singularH1 (Polygon4g (g+1))` is the
homology class of `edgeChain g i` (a 1-cycle once Phase 2's boundary
decomposition lands).

## Status

This file is currently a **stub** — both `edgeHomologyClass` and
`edgeBasisMap` are stated abstractly because they depend on Phase 2's
`singularChainElement_boundary_decomposition` (currently a `True`
stub) to actually construct cycle data and project to homology.

## Concrete construction (when ready)

1. Phase 2's boundary decomposition + Phase 3's
   `edgeSimplex_endpoints_equal` give `edgeChain_isCycle g i`
   as a real equation `d (edgeChain g i) = 0` in
   `SingularChainCoproduct (Polygon4g (g+1)) 0`.
2. The chain group `SingularChain X n` (alias) and
   `SingularChainCoproduct X n` agree by the unfolding of
   `alternatingFaceMapComplex_obj_X` and `sigmaConst`. Identify them
   so `edgeChain g i : SingularChain (Polygon4g (g+1)) 1`.
3. The canonical homology projection on the singular chain complex,
   composed with the iso `SingularChain X 1 ≅ underlying type of
   IntegralOneCycle X`, sends the cycle to a class in
   `singularH1 X`.
4. `edgeHomologyClass g i := (this projection) (edgeChain g i)`.
5. `edgeBasisMap g := LinearMap.lsum ℤ (fun _ => ℤ) ℤ
     fun i => (LinearMap.toSpanSingleton ℤ _ (edgeHomologyClass g i))` —
   linear in the coefficient vector.

## Phase 4 leaves

* `edgeHomologyClass_exists` (currently `True` stub).
* `edgeBasisMap_exists` (currently `True` stub).
* `edgeBasisMap_apply_basis` — the i-th basis vector
  `Pi.basisFun ℤ _ i` maps to `edgeHomologyClass g i`.

These leaves are strictly weaker than the original
`polygon4g_succ_singularH1_hurewiczIso` they will eventually displace.
-/

namespace JacobianChallenge.Periods

/-- **Phase 4 stub.** Existence claim for the homology class of the
i-th edge cycle, gated on Phase 2's chain-boundary decomposition. -/
theorem edgeHomologyClass_exists (_g : ℕ) (_i : Fin (2 * (_g + 1))) :
    ∃ _c : singularH1 (Polygon4g (_g + 1)), True :=
  ⟨0, trivial⟩

/-- **Phase 4 stub.** Existence claim for the cellular comparison
linear map `Polygon4gAbelianization g →ₗ[ℤ] singularH1 (Polygon4g (g+1))`.
The actual definition will be `∑ i, v i • edgeHomologyClass g i`
once `edgeHomologyClass` is upgraded from existence-only data to a
concrete value. -/
theorem edgeBasisMap_exists (g : ℕ) :
    ∃ _f : Polygon4gAbelianization g →ₗ[ℤ] singularH1 (Polygon4g (g + 1)),
      True :=
  ⟨0, trivial⟩

/-! ## Roadmap to closure

When Phases 2.5 (boundary decomposition) and 4 (homology class
projection) land, this file's stubs become real. They then power:

* **Phase 5** — `polygon4g_succ_singularH1_isFinite`: discharged from
  spanning of `edgeBasisMap` (its image is `⊤`).
* **Phase 6.a / 6.b** — linear independence + spanning of the edge
  basis (the surjectivity step is left as a single named sub-sorry
  `polygon4g_succ_singularH1_edgeSpanning` if intractable).
* **Phase 7** — `edgeBasisMap` becomes a `LinearEquiv` via
  `LinearEquiv.ofBijective`, displacing the three current sorries
  (`isFinite`, `isTorsionFree`, `finrank_eq`) at once. -/

end JacobianChallenge.Periods
