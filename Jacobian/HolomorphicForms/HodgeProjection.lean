import Jacobian.HolomorphicForms.HodgeLaplacian
import Jacobian.HolomorphicForms.DeRhamComplex
import Jacobian.HolomorphicForms.HodgeStarRS

/-!
# Harmonic projection: H¹_dR ≃ Harm¹ (frontier API)

The Hodge theorem on a compact oriented Riemannian manifold says that
every de Rham cohomology class has a unique harmonic representative:

  H^k_dR(X, ℂ) ≅ Harm^k(X, ℂ)         (orthogonal projection)

Mathlib v4.28.0 lacks the entire elliptic-operator / harmonic-projection
apparatus.  This file decomposes the named obligation
`complexDimDeRhamH1ℂ_eq_analyticHarmonicGenus` (in
`HodgeDecomposition.lean`) into its underlying
elliptic-projection ingredients.

## What this file provides (round 2 refinement)

* `harmonicProjection1` — opaque ℂ-linear map projecting closed
  1-forms onto harmonic 1-forms.
* `harmonicProjection1_image_eq_harmonic` — frontier identity (sorry).
* `harmonicProjection1_kernel_eq_exact` — frontier identity (sorry,
  Hodge orthogonality of d-image and harmonic).
* `harmonicProjection1_descends` — frontier construction.
* `harmonicProjection1_descended_isLinearEquiv` — frontier identity
  (sorry, the Hodge theorem proper at degree 1).

## TOPDOWN role

Splits the Hodge harmonic projection into:
1. existence of the projection (Δ has closed range and finite kernel),
2. orthogonality of d-image and harmonic (Hodge identity),
3. surjectivity onto H¹_dR.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/-- **Frontier opaque.** Harmonic projection on 1-forms: the orthogonal
projector (in the L² inner product) onto the kernel of the Hodge
Laplacian. -/
noncomputable opaque harmonicProjection1
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    SmoothDiffForm 1 X →ₗ[ℂ] HarmonicOneForm X

/-- **Frontier identity (sorry).** The image of `harmonicProjection1`
is all of `HarmonicOneForm X` — i.e. every harmonic form is its own
image (the projector restricts to the identity on its target). -/
theorem harmonicProjection1_surjective
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Function.Surjective (harmonicProjection1 X) := by
  sorry

/-- **Frontier identity (sorry, HODGE ORTHOGONALITY).** Exact 1-forms
project to zero — equivalently, `d`-image is orthogonal to harmonics
in the L² inner product.

Bottom-up content: `(dη, ω)_{L²} = (η, d^* ω)_{L²}` and `d^* ω = 0`
for harmonic `ω`. Integration by parts is the missing piece. -/
theorem harmonicProjection1_vanishes_on_exact
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : SmoothDiffForm 1 X) (hω : ω ∈ ExactForm 0 X) :
    harmonicProjection1 X ω = 0 := by
  sorry

/-- **Frontier identity (sorry).** The harmonic projection vanishes
exactly on exact forms — i.e. `ker harmonicProjection1 = ExactForm 0 X`
restricted to closed forms.

Together with `harmonicProjection1_surjective` this is the **Hodge
theorem in degree 1**. -/
theorem harmonicProjection1_kernel_eq_exact
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : SmoothDiffForm 1 X) (hclosed : exteriorDerivative 1 X ω = 0) :
    harmonicProjection1 X ω = 0 ↔ ω ∈ ExactForm 0 X := by
  sorry

/-- **Frontier identity (sorry, HODGE THEOREM).** The descended
harmonic projection is a ℂ-linear equivalence from H¹_dR to
harmonic 1-forms.

Bottom-up content: combines `harmonicProjection1_surjective`,
`harmonicProjection1_vanishes_on_exact`, and
`harmonicProjection1_kernel_eq_exact`. -/
theorem deRhamH1_isLinearEquiv_harmonic
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    ∃ _ : deRhamH1Cocycle X ≃ₗ[ℂ] HarmonicOneForm X, True := by
  sorry

/-- **Sorry-free assembly.** From the linear equivalence above, the
ℂ-finrank of `deRhamH1Cocycle X` equals
`analyticHarmonicGenus X`. -/
theorem deRhamH1Cocycle_finrank_eq_analyticHarmonicGenus
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Module.finrank ℂ (deRhamH1Cocycle X) = analyticHarmonicGenus X := by
  obtain ⟨e, _⟩ := deRhamH1_isLinearEquiv_harmonic X
  exact e.finrank_eq

/-- **Round-2 sorry-free assembly.** Refines
`complexDimDeRhamH1ℂ_eq_analyticHarmonicGenus` (originally a frontier
sorry in `HodgeDecomposition.lean`) by chaining
`complexDimDeRhamH1ℂ_eq_finrank_cocycle` and the harmonic-projection
isomorphism. -/
theorem complexDimDeRhamH1ℂ_eq_analyticHarmonicGenus_via_cocycle
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    complexDimDeRhamH1ℂ X = analyticHarmonicGenus X := by
  rw [complexDimDeRhamH1ℂ_eq_finrank_cocycle X,
      deRhamH1Cocycle_finrank_eq_analyticHarmonicGenus X]

end JacobianChallenge.HolomorphicForms
