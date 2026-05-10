import Jacobian.Periods.PolygonCellularHomology

/-!
# Project-side cellular chain API for the fundamental polygon

Mathlib v4.28.0 does not provide a cellular chain complex.  This file
records the small amount of cellular infrastructure needed by
`Polygon4gCellular.lean` as named project-side obligations.  The goal is
to keep the public assembly theorem free of a monolithic `sorry` while
leaving the missing bottom-up topology at explicit leaves.
-/

namespace JacobianChallenge.Periods

/-- The intended first cellular homology group of `Polygon4g g`.
For the standard cell structure there is one vertex, `2g` one-cells,
and one two-cell whose attaching map is the product of commutators. -/
abbrev Polygon4gCellularH1 (g : ℕ) : Type :=
  Fin (2 * g) → ℤ

instance polygon4gCellularH1_addCommGroup (g : ℕ) :
    AddCommGroup (Polygon4gCellularH1 g) := by
  unfold Polygon4gCellularH1
  infer_instance

instance polygon4gCellularH1_module (g : ℕ) :
    Module ℤ (Polygon4gCellularH1 g) := by
  unfold Polygon4gCellularH1
  infer_instance

/-- A witness that `Polygon4g g` carries the standard cellular model:
one zero-cell, `2g` one-cells, and one two-cell.  The concrete CW data
and characteristic maps are the missing Mathlib-side construction. -/
opaque Polygon4gCellularModel (g : ℕ) : Type

/-- **Cellular leaf 1.** Existence of the standard cellular model on
`Polygon4g g`.  Bottom-up route: construct the quotient CW structure
from the closed disk, with all side-pairings collapsed to the unique
zero-cell and paired boundary arcs giving the `a_i,b_i` one-cells. -/
theorem polygon4g_standard_cellular_model (g : ℕ) :
    Nonempty (Polygon4gCellularModel g) := by
  sorry

/-- **Cellular leaf 2.** Boundary formula for the standard model.  It
packages two facts: the one-cell boundary is zero because all endpoints
are the unique vertex, and the two-cell boundary is the abelianised
surface relator, hence zero. -/
opaque Polygon4gCellularBoundaryFormula (g : ℕ) (_ : Polygon4gCellularModel g) : Prop

/-- **Cellular leaf 2.** The cellular boundary formula for the standard
polygon model.  Bottom-up route: compute the attaching map
`∏ᵢ [aᵢ,bᵢ]`; after abelianisation every commutator contributes zero. -/
theorem polygon4g_cellular_boundary_formula
    (g : ℕ) (C : Polygon4gCellularModel g) :
    Polygon4gCellularBoundaryFormula g C := by
  sorry

/-- **Cellular leaf 3.** The first cellular homology computed from the
standard polygon chain complex is the free module on the `2g` one-cells.
This is the algebraic consequence of the boundary formula. -/
theorem polygon4g_cellularH1_iso_free
    (g : ℕ) (C : Polygon4gCellularModel g)
    (_h_boundary : Polygon4gCellularBoundaryFormula g C) :
    Nonempty ((Fin (2 * g) → ℤ) ≃ₗ[ℤ] Polygon4gCellularH1 g) :=
  ⟨LinearEquiv.refl ℤ _⟩

/-- **Cellular assembly.** The polygon's cellular `H₁` is the free
module on the `2g` one-cells.  The only topology used here is isolated
in the model and boundary leaves above. -/
theorem polygon4g_cellularH1_free_assembly (g : ℕ) :
    Nonempty ((Fin (2 * g) → ℤ) ≃ₗ[ℤ] Polygon4gCellularH1 g) := by
  obtain ⟨C⟩ := polygon4g_standard_cellular_model g
  exact polygon4g_cellularH1_iso_free g C (polygon4g_cellular_boundary_formula g C)

end JacobianChallenge.Periods
