import Jacobian.Periods.CellularChainComplex

/-!
# Project-side Hurewicz and cellular-to-singular bridge

This file names the comparison theorem missing from Mathlib v4.28.0:
cellular homology agrees with singular homology for the cellular model
of the fundamental polygon.  It is deliberately stated at the narrow
surface needed by the Jacobian project.
-/

namespace JacobianChallenge.Periods

/-- The comparison data between the cellular chain complex of the
standard polygon model and singular chains on the quotient surface.

Bottom-up route: define the characteristic-map pushforward on cells,
or specialise the usual cellular filtration construction to the finite
CW complex with one zero-cell, `2g` one-cells, and one two-cell. -/
opaque Polygon4gCellularSingularComparisonData
    (g : ℕ) (_C : Polygon4gCellularModel g) : Type

/-- **Comparison leaf 1.** Existence of the cellular-to-singular
comparison data for the standard polygonal cell structure. -/
theorem polygon4g_cellular_singular_comparison_data
    (g : ℕ) (C : Polygon4gCellularModel g)
    (_h_boundary : Polygon4gCellularBoundaryFormula g C) :
    Nonempty (Polygon4gCellularSingularComparisonData g C) := by
  sorry

/-- Correctness of the comparison data: it is compatible with the
cellular and singular differentials and computes the intended attaching
maps in dimensions `0`, `1`, and `2`. -/
opaque Polygon4gCellularSingularChainMapCorrect
    (g : ℕ) (C : Polygon4gCellularModel g)
    (_h_boundary : Polygon4gCellularBoundaryFormula g C)
    (_D : Polygon4gCellularSingularComparisonData g C) : Prop

/-- **Comparison leaf 2.** The chosen comparison data gives the correct
chain-level cellular-to-singular comparison map. -/
theorem polygon4g_cellular_singular_chain_map_correct
    (g : ℕ) (C : Polygon4gCellularModel g)
    (h_boundary : Polygon4gCellularBoundaryFormula g C)
    (D : Polygon4gCellularSingularComparisonData g C) :
    Polygon4gCellularSingularChainMapCorrect g C h_boundary D := by
  sorry

/-- **Comparison leaf 3.** A correct cellular-to-singular comparison map
induces the expected isomorphism on first homology.  Bottom-up route:
specialise the cellular homology theorem / filtration argument to this
finite two-dimensional CW complex. -/
theorem polygon4g_cellular_singular_H1_iso_of_chain_map
    (g : ℕ) (C : Polygon4gCellularModel g)
    (h_boundary : Polygon4gCellularBoundaryFormula g C)
    (D : Polygon4gCellularSingularComparisonData g C)
    (_h_correct : Polygon4gCellularSingularChainMapCorrect g C h_boundary D) :
    Nonempty (Polygon4gCellularH1 g ≃ₗ[ℤ] singularH1 (Polygon4g g)) := by
  sorry

/-- **Comparison assembly.** Cellular homology of the standard
polygonal CW model agrees with singular homology.  This theorem is now
sorry-free; the remaining bottom-up comparison work is isolated in the
three leaves above. -/
theorem polygon4g_cellular_to_singularH1_comparison
    (g : ℕ) (C : Polygon4gCellularModel g)
    (_h_boundary : Polygon4gCellularBoundaryFormula g C) :
    Nonempty (Polygon4gCellularH1 g ≃ₗ[ℤ] singularH1 (Polygon4g g)) :=
by
  obtain ⟨D⟩ := polygon4g_cellular_singular_comparison_data g C _h_boundary
  exact polygon4g_cellular_singular_H1_iso_of_chain_map g C _h_boundary D
    (polygon4g_cellular_singular_chain_map_correct g C _h_boundary D)

/-- **Hurewicz/cellular bridge assembly.** A named project-side
comparison from the computed cellular group to singular `H₁`. -/
theorem polygon4g_cellularH1_to_singularH1 (g : ℕ) :
    Nonempty (Polygon4gCellularH1 g ≃ₗ[ℤ] singularH1 (Polygon4g g)) := by
  obtain ⟨C⟩ := polygon4g_standard_cellular_model g
  exact polygon4g_cellular_to_singularH1_comparison g C
    (polygon4g_cellular_boundary_formula g C)

end JacobianChallenge.Periods
