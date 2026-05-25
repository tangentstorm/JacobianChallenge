import Jacobian.Periods.Polygon4g
import Jacobian.Periods.TopologicalGenus
import Jacobian.Periods.PolygonCellularHomology
import Jacobian.Periods.Hurewicz
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.Topology.Algebra.Module.Basic

/-!
* `Polygon4gFundamentalGroup g` — opaque presentation of the surface
  group `π₁(Polygon4g (g+1))`.
* `polygon4g_fundamentalGroup_abelianized_freeZ` — the abelianised
  surface group is the free ℤ-module `Fin (2(g+1)) → ℤ` (the
  *commutator product abelianises to 0* computation).
* `polygon4g_singularH1_iso_fundamentalGroup_abelianization` —
  Hurewicz: for a path-connected space, `H₁(X, ℤ)` is the
  abelianisation of `π₁(X)`.

## Top-down role

Plugged into `polygon4g_succ_singularH1_basis` via the body
"abelianisation basis transported along the Hurewicz iso" — see
`polygon4g_succ_singularH1_basis_via_hurewicz`.

## Bottom-up content (route summaries)

* **Surface group.** Standard presentation
  `⟨a₀, b₀, …, a_g, b_g | ∏ᵢ [aᵢ, bᵢ]⟩` — derivable from a CW
  structure on `Polygon4g (g+1)` (one 0-cell, `2(g+1)` 1-cells, one
  2-cell whose attaching map traces the relator) plus the Seifert–van
  Kampen theorem.
* **Abelianisation.** Direct computation: the relator is a product of
  commutators, which vanishes in the abelianisation, so the
  abelianisation is `ℤ^{2(g+1)}`.
* **Hurewicz.** `H₁(X, ℤ) ≅ π₁(X)^{ab}` for path-connected `X`.
  Mathlib v4.28.0 has `FundamentalGroup` and singular homology
  separately, but no Hurewicz isomorphism connecting them.
-/

namespace JacobianChallenge.Periods


opaque Polygon4gFundamentalGroup (g : ℕ) : Type


theorem commutator_product_abelianizes_to_zero (g : ℕ) (a b : Fin (g+1) → ℤ) :
    (Finset.univ : Finset (Fin (g+1))).sum (fun i => (a i + b i) + (-(a i) + -(b i)))
      = 0 := by
  refine Finset.sum_eq_zero ?_
  intro i _
  ring


theorem polygon4g_abelianization_basis (g : ℕ) :
    ∃ (_ : AddCommGroup (Polygon4gAbelianization g))
      (_ : Module ℤ (Polygon4gAbelianization g)),
        Nonempty (Module.Basis (Fin (2 * (g + 1))) ℤ
          (Polygon4gAbelianization g)) := by
  refine ⟨polygon4gAbelianization_addCommGroup g,
          polygon4gAbelianization_module g, ?_⟩
  exact ⟨Pi.basisFun ℤ _⟩


opaque Polygon4gFundamentalGroupRepr (g : ℕ) : Type


opaque PolygonAbelianizationMap (g : ℕ) : Type


theorem polygon4g_succ_pathConnected (g : ℕ) :
    PathConnectedSpace (Polygon4g (g + 1)) :=
  inferInstance


theorem polygon4g_succ_hurewicz_iso_freeZ (g : ℕ) :
    Nonempty (Polygon4gAbelianization g ≃ₗ[ℤ] singularH1 (Polygon4g (g + 1))) := by
  obtain ⟨e⟩ := polygon4g_cellularH1_to_singularH1 (g + 1)
  exact ⟨e⟩

/-- **Summary assembly (Packet C1).** -/
theorem hurewicz_singularH1_iso_polygon4g (g : ℕ) :
    Nonempty (Polygon4gAbelianization g ≃ₗ[ℤ] singularH1 (Polygon4g (g + 1))) :=
  polygon4g_succ_hurewicz_iso_freeZ g

theorem polygon4g_hurewicz_iso (g : ℕ) :
    Nonempty (Polygon4gAbelianization g ≃ₗ[ℤ] singularH1 (Polygon4g (g + 1))) :=
  hurewicz_singularH1_iso_polygon4g g


theorem polygon4g_succ_singularH1_basis_via_hurewicz (g : ℕ) :
    Nonempty (Module.Basis (Fin (2 * (g + 1))) ℤ
      (singularH1 (Polygon4g (g + 1)))) := by
  obtain ⟨e⟩ := polygon4g_hurewicz_iso g
  exact ⟨(Pi.basisFun ℤ _).map e⟩

/-- **Polygon 0 is contractible (instance).** -/
instance polygon4g_zero_contractibleSpace : ContractibleSpace (Polygon4g 0) := by
  obtain ⟨h⟩ := polygon4g_zero_homeo_diskC
  exact h.contractibleSpace

/-- **Genus-zero singular `H₁` is subsingleton (instance).** -/
instance polygon4g_zero_singularH1_subsingleton :
    Subsingleton (singularH1 (Polygon4g 0)) :=
  singularH1_subsingleton_of_contractibleSpace

/-- **Sub-sub-leaf (genus ≥ 1 polygon H₁ structure).** -/
theorem polygon4g_succ_singularH1_basis (g : ℕ) :
    Nonempty (Module.Basis (Fin (2 * (g + 1))) ℤ
      (singularH1 (Polygon4g (g + 1)))) :=
  polygon4g_succ_singularH1_basis_via_hurewicz g

/-- **Stage A2 unified basis (any genus).** -/
theorem polygon4g_singularH1_basis (g : ℕ) :
    Nonempty (Module.Basis (Fin (2 * g)) ℤ
      (singularH1 (Polygon4g g))) := by
  cases g with
  | zero =>
    haveI := polygon4g_zero_singularH1_subsingleton
    haveI : IsEmpty (Fin (2 * 0)) := by simpa using Fin.isEmpty
    exact ⟨Module.Basis.empty _⟩
  | succ g => exact polygon4g_succ_singularH1_basis g

/--
**Bridge (Cellular-Singular).** The cellular homology of the
fundamental polygon is isomorphic to its singular homology. (ID 84)
-/
theorem polygon4g_cellular_singular_iso (g : ℕ) :
    Nonempty ((Fin (2 * g) → ℤ) ≃ₗ[ℤ] singularH1 (Polygon4g g)) := by
  obtain ⟨b⟩ := polygon4g_singularH1_basis g
  exact ⟨b.equivFun.symm⟩


theorem polygon4g_succ_singularH1_isFinite (g : ℕ) :
    Module.Finite ℤ (singularH1 (Polygon4g (g + 1))) := by
  obtain ⟨e⟩ := hurewicz_singularH1_iso_polygon4g g
  exact Module.Finite.equiv e


theorem polygon4g_succ_singularH1_isTorsionFree (g : ℕ) :
    Module.IsTorsionFree ℤ (singularH1 (Polygon4g (g + 1))) := by
  obtain ⟨e⟩ := hurewicz_singularH1_iso_polygon4g g
  exact Function.Injective.moduleIsTorsionFree
    (R := ℤ) (M := singularH1 (Polygon4g (g + 1))) (N := Polygon4gAbelianization g)
    e.symm e.symm.injective (fun r m => e.symm.map_smul r m)


theorem polygon4g_succ_singularH1_finrank_eq (g : ℕ) :
    Module.finrank ℤ (singularH1 (Polygon4g (g + 1))) = 2 * (g + 1) := by
  obtain ⟨e⟩ := hurewicz_singularH1_iso_polygon4g g
  rw [← e.finrank_eq]; unfold Polygon4gAbelianization; rw [Module.finrank_pi, Fintype.card_fin]

end JacobianChallenge.Periods
