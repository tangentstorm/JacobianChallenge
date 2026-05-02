import Jacobian.Periods.SurfaceClassification
import Jacobian.Periods.SmoothRealStructure
import Jacobian.Periods.ComplexManifoldOrientable

/-!
# Round 56 — `h1_has_even_basis` via surface classification

Refines the Stage B frontier leaf
`JacobianChallenge.Periods.h1_has_even_basis` (in
`Jacobian.Periods.PeriodFunctional`) by *meeting in the middle* with
the Stage A surface-classification API:

* Apply `ChartedSpaceComplex_to_smoothReal2` (Stage B1, real proof) to
  promote the complex 1-manifold to a smooth real 2-manifold.
* Apply `complexManifold_orientable` (Stage B2, instance) to register
  `Orientable X`.
* Apply `singularH1_basis_of_compactOrientableSurface` (the Round 43
  Stage A corollary) to obtain a basis indexed by
  `Fin (2 * topologicalGenus X)`.
* Pack `g := topologicalGenus X` into the existential.

This factors the Stage B sorry through Stage A's already-decomposed
infrastructure: the only `sorry`s the route inherits are Stage A's
five surface-classification leaves (Rounds 47–54) — *not* a
Stage B-specific blocker.
-/

namespace JacobianChallenge.Periods

open scoped Manifold

/-- **Round 56 / Stage B leaf (h1_has_even_basis via surface
classification, sorry-free).** A compact connected Riemann surface
admits a ℤ-basis of singular `H₁` indexed by `Fin (2g)` for some
`g : ℕ` — namely `g := topologicalGenus X`. -/
theorem h1_has_even_basis_via_surface_classification
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    ∃ g : ℕ, Nonempty (Module.Basis (Fin (2 * g)) ℤ (IntegralOneCycle X)) := by
  obtain ⟨srStruct⟩ := ChartedSpaceComplex_to_smoothReal2 X
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) X := srStruct.chartedSpace
  letI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) X := srStruct.isManifold
  haveI : Orientable X := complexManifold_orientable X
  obtain ⟨b⟩ := singularH1_basis_of_compactOrientableSurface X
  exact ⟨topologicalGenus X, ⟨b⟩⟩

end JacobianChallenge.Periods
