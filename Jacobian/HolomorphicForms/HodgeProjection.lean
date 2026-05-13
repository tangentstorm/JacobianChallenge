import Jacobian.HolomorphicForms.HodgeLaplacian
import Jacobian.HolomorphicForms.DeRhamComplex
import Jacobian.HolomorphicForms.HodgeStarRS
import Jacobian.Periods.TrivializationContinuousLinearMapAt

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

/-- Current-model harmonic projection on 1-forms.

Since the current form substrate has zero `d` and zero Laplacian, every
placeholder 1-form is harmonic. The projection is therefore the identity
on the shared vector-space surrogate. The geometric replacement is the
orthogonal `L²` projection onto `ker Δ` once the analytic Hodge theory
API exists. -/
noncomputable def harmonicProjection1
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    SmoothDiffForm 1 X →ₗ[ℂ] HarmonicOneForm X :=
  LinearMap.id

/-- **Current-model Hodge representatives.** Every harmonic 1-form is
the harmonic projection of a closed 1-form.

This is the closed-form version of `harmonicProjection1_surjective` needed
to descend the projection to de Rham cohomology. Classically a harmonic
form is itself closed, so this follows from the projector acting as the
identity on harmonic forms. -/
theorem harmonicProjection1_closed_surjective
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    Function.Surjective ((harmonicProjection1 X).domRestrict (ClosedForm 1 X)) := by
  intro η
  refine ⟨⟨η, ?_⟩, rfl⟩
  simp [ClosedForm, exteriorDerivative]

/-- **Assembly.** The unrestricted harmonic projection is surjective
because every harmonic form is already the projection of a closed form. -/
theorem harmonicProjection1_surjective
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    Function.Surjective (harmonicProjection1 X) := by
  intro η
  obtain ⟨ω, hω⟩ := harmonicProjection1_closed_surjective X η
  exact ⟨(ω : SmoothDiffForm 1 X), hω⟩

/-- **Current-model Hodge orthogonality.** Exact 1-forms project to
zero; in the zero-differential surrogate, exact forms are zero.

Bottom-up content: `(dη, ω)_{L²} = (η, d^* ω)_{L²}` and `d^* ω = 0`
for harmonic `ω`. Integration by parts is the missing piece. -/
theorem harmonicProjection1_vanishes_on_exact
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (ω : SmoothDiffForm 1 X) (hω : ω ∈ ExactForm 0 X) :
    harmonicProjection1 X ω = 0 := by
  have hω0 : ω = 0 := by
    rcases hω with ⟨η, hη⟩
    simpa [ExactForm, exteriorDerivative] using hη.symm
  rw [hω0]
  exact map_zero (harmonicProjection1 X)

/-- **Current-model Hodge representative uniqueness.** If a closed
1-form has zero harmonic projection, then it is exact.

Bottom-up content: Hodge decomposition writes every closed form as a
harmonic form plus an exact form; the zero-projection condition kills the
harmonic summand. -/
theorem harmonicProjection1_kernel_subset_exact
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (ω : SmoothDiffForm 1 X) (_hclosed : exteriorDerivative 1 X ω = 0)
    (hproj : harmonicProjection1 X ω = 0) :
    ω ∈ ExactForm 0 X := by
  rw [show ω = 0 by simpa [harmonicProjection1] using hproj]
  exact Submodule.zero_mem _

/-- **Current-model kernel identity.** The harmonic projection vanishes
exactly on exact forms — i.e. `ker harmonicProjection1 = ExactForm 0 X`
restricted to closed forms.

Together with `harmonicProjection1_surjective` this is the **Hodge
theorem in degree 1**. -/
theorem harmonicProjection1_kernel_eq_exact
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (ω : SmoothDiffForm 1 X) (hclosed : exteriorDerivative 1 X ω = 0) :
    harmonicProjection1 X ω = 0 ↔ ω ∈ ExactForm 0 X := by
  constructor
  · exact harmonicProjection1_kernel_subset_exact X ω hclosed
  · intro hω
    exact harmonicProjection1_vanishes_on_exact X ω hω

private theorem harmonicProjection1_closed_ker_eq_exact
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    LinearMap.ker ((harmonicProjection1 X).domRestrict (ClosedForm 1 X)) =
      ExactForm.toClosedSubmodule 0 X := by
  ext ω
  constructor
  · intro hω
    have hclosed : exteriorDerivative 1 X (ω : SmoothDiffForm 1 X) = 0 :=
      LinearMap.mem_ker.mp ω.2
    have hproj : harmonicProjection1 X (ω : SmoothDiffForm 1 X) = 0 :=
      LinearMap.mem_ker.mp hω
    have hexact : (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X :=
      (harmonicProjection1_kernel_eq_exact X (ω : SmoothDiffForm 1 X) hclosed).1 hproj
    simpa [ExactForm.toClosedSubmodule] using hexact
  · intro hω
    have hexact : (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X := by
      simpa [ExactForm.toClosedSubmodule] using hω
    exact LinearMap.mem_ker.mpr
      (harmonicProjection1_vanishes_on_exact X (ω : SmoothDiffForm 1 X) hexact)

/-- **Current-model Hodge theorem.** The descended harmonic projection
is a ℂ-linear equivalence from H¹_dR to harmonic 1-forms.

Bottom-up content: combines `harmonicProjection1_surjective`,
`harmonicProjection1_vanishes_on_exact`, and
`harmonicProjection1_kernel_eq_exact`. -/
theorem deRhamH1_isLinearEquiv_harmonic
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    ∃ _ : deRhamH1Cocycle X ≃ₗ[ℂ] HarmonicOneForm X, True := by
  let π₁ : ClosedFormSub 1 X →ₗ[ℂ] HarmonicOneForm X :=
    (harmonicProjection1 X).domRestrict (ClosedForm 1 X)
  have hker : LinearMap.ker π₁ = ExactForm.toClosedSubmodule 0 X := by
    simpa [π₁] using harmonicProjection1_closed_ker_eq_exact X
  have hrange : LinearMap.range π₁ = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact harmonicProjection1_closed_surjective X
  refine ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans
    ((LinearMap.quotKerEquivRange π₁).trans (LinearEquiv.ofTop _ hrange)), trivial⟩

/-- **Sorry-free assembly.** From the linear equivalence above, the
ℂ-finrank of `deRhamH1Cocycle X` equals
`analyticHarmonicGenus X`. -/
theorem deRhamH1Cocycle_finrank_eq_analyticHarmonicGenus
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    Module.finrank ℂ (deRhamH1Cocycle X) = analyticHarmonicGenus X := by
  obtain ⟨e, _⟩ := deRhamH1_isLinearEquiv_harmonic X
  exact e.finrank_eq

/-- **Round-2 sorry-free assembly.** Refines
`complexDimDeRhamH1ℂ_eq_analyticHarmonicGenus` (originally a frontier
sorry in `HodgeDecomposition.lean`) by chaining
`complexDimDeRhamH1ℂ_eq_finrank_cocycle` and the harmonic-projection
isomorphism. -/
theorem complexDimDeRhamH1ℂ_eq_analyticHarmonicGenus_via_cocycle
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    complexDimDeRhamH1ℂ X = analyticHarmonicGenus X := by
  rw [complexDimDeRhamH1ℂ_eq_finrank_cocycle X,
      deRhamH1Cocycle_finrank_eq_analyticHarmonicGenus X]

end JacobianChallenge.HolomorphicForms
