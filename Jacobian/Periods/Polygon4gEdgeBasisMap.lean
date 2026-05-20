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
  the `edgeChainCoeff` route).
* **Phase 6.b** — spanning (via the lift-to-disk shortcut).
* **Phase 7** — `edgeBasisMap` becomes a `LinearEquiv` via
  `LinearEquiv.ofBijective`, displacing the three current sorries
  (`isFinite`, `isTorsionFree`, `finrank_eq`) at once.
-/

namespace JacobianChallenge.Periods

open AlgebraicTopology CategoryTheory

/-- **Phase 4 stub (existence form, kept for backwards compatibility).** -/
theorem edgeBasisMap_exists (g : ℕ) :
    ∃ f : Polygon4gAbelianization g →ₗ[ℤ] singularH1 (Polygon4g (g + 1)),
      f = edgeBasisMap g :=
  ⟨edgeBasisMap g, rfl⟩

/-- **Phase 4 stub.** Existence of edge homology classes (kept for
backwards compatibility). -/
theorem edgeHomologyClass_exists (g : ℕ) (i : Fin (2 * (g + 1))) :
    ∃ c : singularH1 (Polygon4g (g + 1)), c = edgeHomologyClass g i :=
  ⟨edgeHomologyClass g i, rfl⟩

/-- The existing concrete edge homology class agrees with the Hurewicz
project-side edge-chain class map on a single cellular edge generator.
This is the bridge needed to transport future cellular/Hurewicz spanning
statements to the concrete `edgeHomologyFamily`. -/
theorem edgeHomologyClass_eq_toSingularH1Class_single
    (g : ℕ) (C : Polygon4gCellularModel (g + 1))
    (D : Polygon4gCellularSingularComparisonData (g + 1) C)
    (i : Fin (2 * (g + 1))) :
    edgeHomologyClass g i =
      Polygon4gSingularC1.toSingularH1Class (g + 1) C D ⟨Pi.single i 1⟩ := by
  rw [Polygon4gSingularC1.toSingularH1_single]
  rfl

/-- The coefficient map from the project-side singular one-chain wrapper
to the free module on polygon edges. -/
noncomputable def polygon4gSingularC1CoeffMap
    (g : ℕ) (C : Polygon4gCellularModel (g + 1))
    (D : Polygon4gCellularSingularComparisonData (g + 1) C) :
    Polygon4gSingularC1 (g + 1) C D →ₗ[ℤ] Polygon4gAbelianization g where
  toFun := fun c => c.coeff
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro n x
    rfl

/-- The project-side singular one-chain wrapper is linearly equivalent
to the free coefficient module on the polygon edges. -/
noncomputable def polygon4gSingularC1CoeffLinearEquiv
    (g : ℕ) (C : Polygon4gCellularModel (g + 1))
    (D : Polygon4gCellularSingularComparisonData (g + 1) C) :
    Polygon4gSingularC1 (g + 1) C D ≃ₗ[ℤ] Polygon4gAbelianization g where
  toFun := fun c => c.coeff
  invFun := fun v => ⟨v⟩
  left_inv := by
    intro c
    ext i
    rfl
  right_inv := by
    intro v
    rfl
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro n x
    rfl

/-- The coefficient linear map is the linear map underlying the
coefficient equivalence. -/
theorem polygon4gSingularC1CoeffMap_eq_equiv_toLinearMap
    (g : ℕ) (C : Polygon4gCellularModel (g + 1))
    (D : Polygon4gCellularSingularComparisonData (g + 1) C) :
    polygon4gSingularC1CoeffMap g C D =
      (polygon4gSingularC1CoeffLinearEquiv g C D).toLinearMap := by
  ext c
  rfl

/-- The linear edge-class realization of the project-side singular
one-chain wrapper: read off its edge coefficients, then form the
corresponding finite linear combination of concrete edge homology
classes. -/
noncomputable def polygon4gSingularC1EdgeClassMap
    (g : ℕ) (C : Polygon4gCellularModel (g + 1))
    (D : Polygon4gCellularSingularComparisonData (g + 1) C) :
    Polygon4gSingularC1 (g + 1) C D →ₗ[ℤ] singularH1 (Polygon4g (g + 1)) :=
  (edgeBasisMap g).comp (polygon4gSingularC1CoeffMap g C D)

/-- The linear edge-class realization is exactly `edgeBasisMap` applied
to the wrapper coefficients. -/
theorem polygon4gSingularC1EdgeClassMap_apply
    (g : ℕ) (C : Polygon4gCellularModel (g + 1))
    (D : Polygon4gCellularSingularComparisonData (g + 1) C)
    (c : Polygon4gSingularC1 (g + 1) C D) :
    polygon4gSingularC1EdgeClassMap g C D c = edgeBasisMap g c.coeff :=
  rfl

/-- Surjectivity of the project-side edge-class realization is equivalent
to surjectivity of the concrete edge-basis map. -/
theorem polygon4gSingularC1EdgeClassMap_surjective_iff_edgeBasisMap_surjective
    (g : ℕ) (C : Polygon4gCellularModel (g + 1))
    (D : Polygon4gCellularSingularComparisonData (g + 1) C) :
    Function.Surjective (polygon4gSingularC1EdgeClassMap g C D) ↔
      Function.Surjective (edgeBasisMap g) := by
  constructor
  · intro h y
    obtain ⟨c, hc⟩ := h y
    exact ⟨c.coeff, by simpa [polygon4gSingularC1EdgeClassMap_apply] using hc⟩
  · intro h y
    obtain ⟨v, hv⟩ := h y
    exact ⟨⟨v⟩, by simpa [polygon4gSingularC1EdgeClassMap_apply] using hv⟩

/-
`edgeBasisMap g` evaluated on a standard basis vector `Pi.single i 1`
yields `edgeHomologyClass g i`.
-/
theorem edgeBasisMap_single (g : ℕ) (i : Fin (2 * (g + 1))) :
    edgeBasisMap g (Pi.single i 1) = edgeHomologyClass g i := by
  unfold edgeBasisMap;
  simp +decide [ LinearMap.toSpanSingleton, LinearMap.proj ]

/-- On project-side edge generators, the linear edge-class realization
agrees with the concrete Hurewicz class map. -/
theorem polygon4gSingularC1EdgeClassMap_single_eq_toSingularH1Class
    (g : ℕ) (C : Polygon4gCellularModel (g + 1))
    (D : Polygon4gCellularSingularComparisonData (g + 1) C)
    (i : Fin (2 * (g + 1))) :
    polygon4gSingularC1EdgeClassMap g C D ⟨Pi.single i 1⟩ =
      Polygon4gSingularC1.toSingularH1Class (g + 1) C D ⟨Pi.single i 1⟩ := by
  rw [polygon4gSingularC1EdgeClassMap_apply, edgeBasisMap_single,
    edgeHomologyClass_eq_toSingularH1Class_single]

/-- The linearized project-side singular-C1 map agrees with the concrete
edge-class realization. -/
theorem polygon4g_toSingularH1LinearMap_eq_edgeClassMap
    (g : ℕ) (C : Polygon4gCellularModel (g + 1))
    (D : Polygon4gCellularSingularComparisonData (g + 1) C) :
    Polygon4gSingularC1.toSingularH1LinearMap (g + 1) C D =
      polygon4gSingularC1EdgeClassMap g C D := by
  ext c
  rw [polygon4gSingularC1EdgeClassMap_apply]
  exact polygon4gSingularC1_toSingularH1LinearMap_apply_succ g C D c

/-- **Edge-class surjectivity leaf.**
The project-side edge-class realization is surjective.  This is the
edge-map form of the lift-to-disk spanning argument: every singular
`H₁` class is homologous to a finite integral linear combination of the
polygon edge loops. -/
theorem polygon4gSingularC1EdgeClassMap_surjective
    (g : ℕ) (C : Polygon4gCellularModel (g + 1))
    (D : Polygon4gCellularSingularComparisonData (g + 1) C) :
    Function.Surjective (polygon4gSingularC1EdgeClassMap g C D) := by
  exact (polygon4gSingularC1EdgeClassMap_surjective_iff_edgeBasisMap_surjective g C D).2
    (edgeBasisMap_surjective g)

/-
The range of `edgeBasisMap g` equals the ℤ-span of the edge
homology family.
-/
theorem edgeBasisMap_range (g : ℕ) :
    LinearMap.range (edgeBasisMap g) = Submodule.span ℤ (Set.range (edgeHomologyFamily g)) := by
  refine' le_antisymm ( LinearMap.range_le_iff_comap.mpr _ ) ( Submodule.span_le.mpr ( Set.range_subset_iff.mpr _ ) );
  · ext x;
    simp +decide [ edgeBasisMap, Submodule.mem_span_range_iff_exists_fun ];
    exact ⟨ _, rfl ⟩;
  · exact fun i => ⟨ Pi.single i 1, edgeBasisMap_single g i ⟩

/-- The edge-family spanning statement is exactly surjectivity of the
concrete edge-basis map.  This isolates the remaining Phase 6.b content
as a statement about the chain-level edge classes, rather than as a
separate abstract spanning obligation. -/
theorem edgeHomologyFamily_spans_iff_edgeBasisMap_surjective (g : ℕ) :
    Submodule.span ℤ (Set.range (edgeHomologyFamily g)) = ⊤ ↔
      Function.Surjective (edgeBasisMap g) := by
  rw [← LinearMap.range_eq_top, edgeBasisMap_range]

/-- The edge-family spanning theorem is equivalent to surjectivity of
the project-side edge-class realization. -/
theorem edgeHomologyFamily_spans_iff_project_edgeClassMap_surjective
    (g : ℕ) (C : Polygon4gCellularModel (g + 1))
    (D : Polygon4gCellularSingularComparisonData (g + 1) C) :
    Submodule.span ℤ (Set.range (edgeHomologyFamily g)) = ⊤ ↔
      Function.Surjective (polygon4gSingularC1EdgeClassMap g C D) := by
  rw [edgeHomologyFamily_spans_iff_edgeBasisMap_surjective,
    polygon4gSingularC1EdgeClassMap_surjective_iff_edgeBasisMap_surjective]

/-- **Phase 6.b spanning leaf.**
The edge homology classes span `singularH1 (Polygon4g (g+1))`.

**Substantive Proof (lift-to-disk shortcut):**
1. Every singular 1-cycle `z` in `Polygon4g` can be lifted to a
   singular 1-chain `z'` in `DiskC` (using the path-lifting property
   of the polygon quotient).
2. The boundary `∂ z'` is a sum of points `p - q` in `DiskC` such that
   `mk p = mk q`.
3. Such points are connected by a path of boundary arcs (edges) in
   `DiskC`.
4. Adding these edge-paths to `z'` yields a 1-cycle `z''` in `DiskC`.
5. Since `DiskC` is contractible, `H₁(DiskC) = 0`, so `z''` is a
   boundary.
6. Projecting back to `Polygon4g`, `z` is homologous to the sum of the
   projections of the edge-paths, which are the `edgeHomologyClass`
   elements. -/
theorem edgeHomologyFamily_spans (g : ℕ) :
    Submodule.span ℤ (Set.range (edgeHomologyFamily g)) = ⊤ := by
  obtain ⟨C⟩ := polygon4g_standard_cellular_model (g + 1)
  let h_boundary := polygon4g_cellular_boundary_formula (g + 1) C
  obtain ⟨D⟩ := polygon4g_cellular_singular_comparison_data (g + 1) C h_boundary
  rw [edgeHomologyFamily_spans_iff_project_edgeClassMap_surjective g C D]
  exact polygon4gSingularC1EdgeClassMap_surjective g C D

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
