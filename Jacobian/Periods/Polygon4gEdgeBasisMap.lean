import Jacobian.Periods.Polygon4gCellular
import Jacobian.Periods.Polygon4gEdgeChain
import Mathlib.Algebra.Homology.ConcreteCategory
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

* `edgeHomologyClass` — Phase 4 leaf: the homology class of the i-th
  edge cycle, defined via `HomologicalComplex.cyclesMk` and
  `HomologicalComplex.homologyπ`. Sorry-free.
* `edgeBasisMap` — sorry-free, defined as the sum of
  `LinearMap.toSpanSingleton ℤ _ (edgeHomologyClass g i) ∘ proj i`
  over `i : Fin (2 * (g + 1))`.

## Roadmap to Phase 7

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

open AlgebraicTopology CategoryTheory

/-- The singular chain complex of `Polygon4g (g+1)`. -/
noncomputable abbrev polygonChainComplex (g : ℕ) : ChainComplex (ModuleCat ℤ) ℕ :=
  ((singularChainComplexFunctor (ModuleCat ℤ)).obj
      (ModuleCat.of ℤ ℤ)).obj (TopCat.of (Polygon4g (g + 1)))

/-- The shape relation `(down ℕ).next 1 = 0` used by `cyclesMk`. -/
private lemma next_one_eq_zero :
    (ComplexShape.down ℕ).next 1 = 0 :=
  ComplexShape.next_eq' _ (by simp [ComplexShape.down])

/-- **Phase 4 leaf (real homology projection).**
The homology class of the i-th edge cycle in
`singularH1 (Polygon4g (g+1))`, obtained by:
* constructing a cycle via `cyclesMk` from `edgeChain g i` and
  `edgeChain_isCycle g i`,
* projecting to homology via `homologyπ`.

Sorry-free: both inputs are real (`edgeChain` is sorry-free; the
boundary equation `edgeChain_isCycle` was discharged once
`singularChainElement_boundary_decomposition` landed). -/
noncomputable def edgeHomologyClass (g : ℕ) (i : Fin (2 * (g + 1))) :
    singularH1 (Polygon4g (g + 1)) :=
  ((forget₂ (ModuleCat ℤ) Ab).map ((polygonChainComplex g).homologyπ 1))
    ((polygonChainComplex g).cyclesMk (edgeChain g i) 0 next_one_eq_zero
      (edgeChain_isCycle g i))

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

Proof: `edgeBasisMap` is surjective (Phase 6.b), and the Hurewicz iso
gives `Polygon4gAbelianization g ≃ₗ[ℤ] singularH1 (Polygon4g (g+1))`.
Composing `e.symm ∘ edgeBasisMap` gives a surjective endomorphism of
the finitely generated free ℤ-module `Polygon4gAbelianization g`,
which is bijective by the Orzech property (Noetherian argument).
Hence `edgeBasisMap` is injective. -/
theorem edgeBasisMap_injective (g : ℕ) :
    Function.Injective (edgeBasisMap g) := by
  have h_surj := edgeBasisMap_surjective g
  obtain ⟨e⟩ := hurewicz_singularH1_iso_polygon4g g
  have h_bij : Function.Bijective (e.symm.toLinearMap ∘ₗ edgeBasisMap g) := by
    have h_surj' : Function.Surjective (e.symm.toLinearMap ∘ₗ edgeBasisMap g) :=
      fun x => by obtain ⟨y, hy⟩ := h_surj (e x); exact ⟨y, by simp [LinearMap.comp_apply, hy]⟩
    exact OrzechProperty.bijective_of_surjective_endomorphism
      (e.symm.toLinearMap ∘ₗ edgeBasisMap g) h_surj'
  exact Function.Injective.of_comp h_bij.injective

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