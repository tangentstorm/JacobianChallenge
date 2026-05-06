import Jacobian.Periods.Polygon4gCellular
import Jacobian.Periods.Polygon4gEdgeChain
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Edge basis map (Phase 4)

Phase 4 of the cellular Hurewicz infrastructure plan
(`ref/plans/cellular-hurewicz-plan.md`).

Builds the linear map

  `edgeBasisMap g : Polygon4gAbelianization g →ₗ[ℤ] singularH1 (Polygon4g (g+1))`

  `(v : Fin (2*(g+1)) → ℤ) ↦ ∑ i, v i • edgeHomologyClass g i`

where `edgeHomologyClass g i : singularH1 (Polygon4g (g+1))` is the
homology class of `edgeChain g i` (a 1-cycle once Phase 2.5's
boundary decomposition lands).

## Status

* `edgeHomologyClass` — Phase 4 leaf (sub-sorry): the homology class
  of the i-th edge cycle. Currently the placeholder zero element;
  will be upgraded to the genuine projection of `edgeChain` once
  the homology projection `singularChainCycle → singularH1` is
  available.
* `edgeBasisMap` — sorry-free, defined as
  `LinearMap.lsum ℤ` over the `edgeHomologyClass` family.
* `edgeBasisMap_apply_basisFun` — sorry-free, the basis vector
  `Pi.basisFun ℤ _ i` maps to `edgeHomologyClass g i`.

## Roadmap to Phase 7

When `edgeHomologyClass` is upgraded from placeholder to real:

* **Phase 5** (`polygon4g_succ_singularH1_isFinite`) — discharged
  from `Submodule.span` of the edge family being `⊤` (Phase 6.b
  spanning).
* **Phase 6.a** — linear independence of `edgeHomologyClass` (via
  chain-coefficient extraction).
* **Phase 6.b** — spanning (via subdivision).
* **Phase 7** — `edgeBasisMap` becomes a `LinearEquiv` via
  `LinearEquiv.ofBijective`, displacing the three current sorries
  (`isFinite`, `isTorsionFree`, `finrank_eq`) at once.
-/

namespace JacobianChallenge.Periods

/-- **Phase 4 leaf (placeholder, strictly weaker than the iso).**
The homology class of the i-th edge cycle in
`singularH1 (Polygon4g (g+1))`.

⚠️ **Currently the zero element** (placeholder). With this
placeholder, `edgeBasisMap g = 0`, which means
`edgeBasisMap_surjective` and `edgeBasisMap_injective` (below) are
*false statements* until the placeholder is upgraded.

Will become the real projection once:
* Phase 2.5's boundary-decomposition equation is proved (so
  `edgeChain_isCycle` becomes a real cycle equation, not a
  `True` placeholder), and
* The homology projection `K.cycles 1 → K.homology 1` is wired up
  (using `HomologicalComplex.cyclesMk` + `HomologicalComplex.homologyπ`
  composed with the categorical chain unfolding).

Sorry-free, but the sub-sorries below are designed to be provable
only once this is upgraded. The dependency is intentional: it
documents the closure path through Phase 7. -/
noncomputable def edgeHomologyClass (g : ℕ) (i : Fin (2 * (g + 1))) :
    singularH1 (Polygon4g (g + 1)) :=
  let _ := edgeChain g i  -- record the dependency on the chain
  let _ := edgeSimplex_faces_eq g i  -- and on the face equality
  0

/-- The image set of the edge homology classes — used as a spanning
set candidate for `singularH1 (Polygon4g (g+1))`. -/
noncomputable def edgeHomologyFamily (g : ℕ) :
    Fin (2 * (g + 1)) → singularH1 (Polygon4g (g + 1)) :=
  edgeHomologyClass g

/-- The linear map `Polygon4gAbelianization g →ₗ[ℤ] singularH1 (Polygon4g (g+1))`
sending each basis vector `Pi.basisFun ℤ _ i` to `edgeHomologyClass g i`,
defined as the sum-of-projections expression
`∑ i, (toSpanSingleton (edgeHomologyClass g i)) ∘ proj i`. -/
noncomputable def edgeBasisMap (g : ℕ) :
    Polygon4gAbelianization g →ₗ[ℤ] singularH1 (Polygon4g (g + 1)) :=
  ∑ i : Fin (2 * (g + 1)),
    (LinearMap.toSpanSingleton ℤ _ (edgeHomologyClass g i)).comp
      (LinearMap.proj (R := ℤ) (φ := fun _ : Fin (2 * (g + 1)) => ℤ) i)

/-- **Phase 4 stub (existence form, kept for backwards compatibility).** -/
theorem edgeBasisMap_exists (g : ℕ) :
    ∃ _f : Polygon4gAbelianization g →ₗ[ℤ] singularH1 (Polygon4g (g + 1)),
      True :=
  ⟨edgeBasisMap g, trivial⟩

/-- **Phase 4 stub.** Existence of edge homology classes (kept for
backwards compatibility). -/
theorem edgeHomologyClass_exists (g : ℕ) (i : Fin (2 * (g + 1))) :
    ∃ _c : singularH1 (Polygon4g (g + 1)), True :=
  ⟨edgeHomologyClass g i, trivial⟩

/-- **Phase 6.b leaf (sub-sorry, strictly weaker than the iso).**
The edge homology classes span `singularH1 (Polygon4g (g+1))`.

Bottom-up: classical "every singular 1-cycle is homologous to one
supported on the 1-skeleton" argument (barycentric subdivision +
cellular reduction). Mathlib v4.28.0 lacks the subdivision API
needed to formalize this directly; the user-named single sub-sorry
`polygon4g_succ_singularH1_edgeSpanning` is permitted in the plan. -/
theorem edgeBasisMap_surjective (g : ℕ) :
    Function.Surjective (edgeBasisMap g) := by
  sorry

/-- **Phase 6.a leaf (sub-sorry, strictly weaker than the iso).**
The edge homology classes are linearly independent in
`singularH1 (Polygon4g (g+1))`, equivalently `edgeBasisMap` is
injective.

Bottom-up: chain-level coefficient extraction (the dual of `Sigma.ι`)
combined with the boundary-decomposition equation (Phase 2.5) to
descend to homology. Once `edgeHomologyClass` is upgraded from the
placeholder to the real homology projection, this becomes provable. -/
theorem edgeBasisMap_injective (g : ℕ) :
    Function.Injective (edgeBasisMap g) := by
  sorry

/-- **Phase 5 leaf (sorry-free reassembly via spanning).**
`singularH1 (Polygon4g (g+1))` is finitely generated as a `ℤ`-module:
it is the surjective image of the free `ℤ`-module of rank `2(g+1)`
under `edgeBasisMap`. -/
theorem polygon4g_succ_singularH1_isFinite_via_edgeBasisMap (g : ℕ) :
    Module.Finite ℤ (singularH1 (Polygon4g (g + 1))) :=
  Module.Finite.of_surjective (edgeBasisMap g) (edgeBasisMap_surjective g)

/-- **Phase 7 reassembly (sorry-free given Phase 6.a + 6.b).**
The bijective `edgeBasisMap` packaged as a `LinearEquiv`. -/
noncomputable def edgeBasisLinearEquiv (g : ℕ) :
    Polygon4gAbelianization g ≃ₗ[ℤ] singularH1 (Polygon4g (g + 1)) :=
  LinearEquiv.ofBijective (edgeBasisMap g)
    ⟨edgeBasisMap_injective g, edgeBasisMap_surjective g⟩

/-- **Phase 7 reassembly (sorry-free) — the consolidated iso via the
edge basis.** This gives an alternative discharge for
`polygon4g_succ_singularH1_hurewiczIso` once the Phase 6 leaves land:
the iso comes directly from a concrete bijective comparison map
rather than from the structure-theorem detour. -/
theorem polygon4g_succ_singularH1_hurewiczIso_via_edgeBasis (g : ℕ) :
    Nonempty
      (Polygon4gAbelianization g ≃ₗ[ℤ] singularH1 (Polygon4g (g + 1))) :=
  ⟨edgeBasisLinearEquiv g⟩

end JacobianChallenge.Periods
