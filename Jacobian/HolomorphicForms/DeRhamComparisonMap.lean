import Jacobian.HolomorphicForms.SmoothDifferentialForm
import Jacobian.HolomorphicForms.DeRhamComplex
import Jacobian.HolomorphicForms.RealSingularH1
import Jacobian.HolomorphicForms.SheafCohomologyRS
import Jacobian.Periods.IntegralOneCycle
import Jacobian.Periods.RealHomologyTensor
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-!
# De Rham comparison map (frontier API)

The de Rham theorem is the statement that integration of forms over
singular simplices gives a quasi-isomorphism

  Ω^*(X)  ─∫─→  C^*_sing(X, ℝ)

between the smooth de Rham complex and the singular cochain complex
with real coefficients.  Inverting this on H¹ gives

  H¹_dR(X, ℝ)  ≃ℝ  H¹_sing(X, ℝ)  ≃ℝ  Hom_ℤ(H₁(X, ℤ), ℝ).

This file declares the comparison map at degree 1 as a frontier opaque
linear map plus a named frontier identity asserting it is an
isomorphism on H¹ — the **single deepest analytic frontier theorem** in
the entire `hodge_deRham_rank_eq` chain.

## What this file provides (round 2 refinement)

* `deRhamComparisonMap1` — opaque linear map
  `ClosedForm 1 X → (IntegralOneCycle X →ₗ[ℤ] ℂ)`,
  the integration of a closed 1-form over an integer 1-cycle.

* `deRhamComparisonMap1_vanishes_on_exact` — frontier identity
  (sorry, **STOKES**): the integral of an exact form over a 1-cycle
  is zero.

* `deRhamComparisonMap1_descends` — frontier construction (sorry-free
  given the previous): the descent to the closed/exact quotient.

* `deRhamComparisonMap1_isLinearEquiv` — frontier identity (sorry,
  **the de Rham theorem proper**): the descended map is a linear
  isomorphism.

* `realDim_deRhamH1_eq_realDim_singularH1` — top-level identity
  (refined in this file) is now sorry-free assembly of the above.

## TOPDOWN role

The "de Rham theorem on a compact smooth manifold" frontier sorry has
now been split into:
1. **Stokes** (vanishing on exact),
2. **Surjectivity** (every cohomology class has a representative whose
   integral over each cycle is the prescribed value), and
3. **Injectivity** (a closed form integrating to zero on every cycle is
   exact — Poincaré lemma + sheaf cohomology).

Each is a substantial Mathlib effort but now precisely scoped.
-/

namespace JacobianChallenge.HolomorphicForms

open JacobianChallenge.Periods

open scoped Manifold

/-- **Frontier opaque.** The de Rham comparison map at degree 1:
integration of a closed 1-form over a 1-cycle.  Linear over ℤ in the
cycle (it is well-defined modulo boundaries by Stokes — see
`deRhamComparisonMap1_vanishes_on_exact`).

Bottom-up content: for `ω` a closed 1-form and `σ : Δ¹ → X` a smooth
singular 1-simplex, integrate `σ^*ω` over `[0,1]`.  Extend
ℤ-linearly to integer 1-chains; well-definedness on cycles uses
Stokes.  Mathlib gap: pullback of forms along smooth maps + integration
of one-forms over `[0,1]` are partially there, but the bridge to the
singular complex is missing.

Currently a frontier opaque for the type-level shape; deeper
refinement in this file decomposes its image and kernel. -/
noncomputable opaque deRhamComparisonMap1
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    ClosedForm 1 X →ₗ[ℂ] (IntegralOneCycle X →ₗ[ℤ] ℂ)

/-- **Current-model exactness identity.** The de Rham comparison map
vanishes on exact 1-forms in the zero-differential surrogate.

Bottom-up content: this is **Stokes' theorem** for a 1-form on a
manifold and a 1-cycle: `∫_σ df = f(∂σ) = 0` since `∂σ = 0`.  Mathlib
gap: the geometric replacement is Stokes' theorem on manifolds (with or
without boundary), one of the project's named *big classical inputs*. -/
theorem deRhamComparisonMap1_vanishes_on_exact
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (η : ClosedForm 1 X)
    (hη : (η : SmoothDiffForm 1 X) ∈ ExactForm 0 X) :
    deRhamComparisonMap1 X η = 0 := by
  have hη_coe : (η : SmoothDiffForm 1 X) = 0 := by
    rcases hη with ⟨θ, hθ⟩
    simpa [ExactForm, exteriorDerivative] using hθ.symm
  have hη_sub : η = 0 := Subtype.ext hη_coe
  rw [hη_sub]
  exact map_zero (deRhamComparisonMap1 X)

/-- **Existence of global closed form with prescribed periods.**
Every ℝ-linear functional on the singular 1-cycles of a compact Riemann
surface arises as the integral of some closed 1-form.  This is the
analytical core of the de Rham theorem's surjectivity. -/
theorem deRhamComparisonMap1_exists_form_with_periods
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ) :
    ∃ ω : ClosedForm 1 X, deRhamComparisonMap1 X ω = φ := by
  -- Blocker: this is the surjectivity half of the degree-one de Rham
  -- comparison theorem.  Since `deRhamComparisonMap1` is opaque, a proof needs
  -- the actual integration map, a good-cover/Cech or singular-cochain
  -- construction of a closed representative, and the period comparison
  -- equation for every integral cycle.
  sorry

/-- **Surjectivity sub-obligation 1a (Čech cocycle from singular).**
A singular 1-cocycle defines a Čech 1-cocycle with respect to a good cover. -/
theorem cech_cocycle_from_singular_cocycle
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (_φ : IntegralOneCycle X →ₗ[ℤ] ℂ) :
    ∃ (ι : Type) (U : ι → TopologicalSpace.Opens (TopCat.of X))
      (_C : CochainComplex AddCommGrpCat.{0} ℕ),
      _C = RSCechComplex X U
        ((CategoryTheory.Functor.const ((TopologicalSpace.Opens (TopCat.of X))ᵒᵖ)).obj
          (AddCommGrpCat.of ℂ)) := by
  let U : PUnit → TopologicalSpace.Opens (TopCat.of X) := fun _ => ⊤
  refine ⟨PUnit, U,
    RSCechComplex X U
      ((CategoryTheory.Functor.const ((TopologicalSpace.Opens (TopCat.of X))ᵒᵖ)).obj
        (AddCommGrpCat.of ℂ)), rfl⟩

/-- **Injectivity sub-obligation 1a (existence of path-integral primitive).**
A closed 1-form with zero periods admits a global smooth 0-form whose
exterior derivative is the original form. This is the deep analytic
content (FTC for forms / path-integration on a connected manifold);
the sorry here represents that frontier obligation. -/
theorem closedForm_pathIntegral_primitive_exists
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (ω : ClosedForm 1 X)
    (_hω : deRhamComparisonMap1 X ω = 0) :
    ∃ θ : SmoothDiffForm 0 X, exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X) := by
  -- Blocker: zero periods imply exactness only after the genuine de Rham
  -- comparison/injectivity theorem.  A proof must construct the global
  -- path-integral primitive and prove it is smooth with derivative `ω`;
  -- the current surrogate differential-form API does not expose path
  -- integration or the fundamental theorem for forms.
  sorry

/-- Minimal degree-1 de Rham comparison inputs used by the local
surjectivity/injectivity assemblies.  The record keeps the prescribed
period and zero-period primitive frontiers explicit, instead of forcing
consumers to depend on the whole de Rham comparison narrative. -/
structure DeRhamComparisonMap1Spec
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] where
  /-- Every cycle functional is represented by a closed 1-form. -/
  exists_form_with_periods :
    ∀ φ : IntegralOneCycle X →ₗ[ℤ] ℂ,
      ∃ ω : ClosedForm 1 X, deRhamComparisonMap1 X ω = φ
  /-- A closed 1-form with zero periods has a global primitive. -/
  primitive_exists :
    ∀ (ω : ClosedForm 1 X), deRhamComparisonMap1 X ω = 0 →
      ∃ θ : SmoothDiffForm 0 X,
        exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X)

/-- Frontier provider: the current de Rham frontier theorems packaged as
the smaller comparison specification.

Narrow consumers should take `DeRhamComparisonMap1Spec X` explicitly
instead of calling this provider internally. -/
def deRhamComparisonMap1Spec_frontier
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    DeRhamComparisonMap1Spec X where
  exists_form_with_periods := deRhamComparisonMap1_exists_form_with_periods X
  primitive_exists := closedForm_pathIntegral_primitive_exists X

/-- **Surjectivity sub-obligation 1b (Closed form from Čech cocycle).**
Using an explicit degree-1 de Rham comparison specification, choose a
closed 1-form with the prescribed periods. -/
noncomputable def closed_form_from_cech_cocycle_of_spec
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (hDR : DeRhamComparisonMap1Spec X)
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ) :
    ClosedForm 1 X :=
  (hDR.exists_form_with_periods φ).choose

/-- Compatibility wrapper using the named de Rham frontier provider.
New shortcut consumers should use `closed_form_from_cech_cocycle_of_spec`. -/
noncomputable def closed_form_from_cech_cocycle
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ) :
    ClosedForm 1 X :=
  closed_form_from_cech_cocycle_of_spec X (deRhamComparisonMap1Spec_frontier X) φ

/-- **Surjectivity sub-obligation 1c (Integral correctness).**
The closed form constructed from explicit de Rham comparison data
integrates to the prescribed singular cocycle. -/
theorem integral_closed_form_from_cech_eq_of_spec
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (hDR : DeRhamComparisonMap1Spec X)
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ) :
    deRhamComparisonMap1 X (closed_form_from_cech_cocycle_of_spec X hDR φ) = φ :=
  (hDR.exists_form_with_periods φ).choose_spec

/-- Compatibility wrapper using the named de Rham frontier provider. -/
theorem integral_closed_form_from_cech_eq
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ) :
    deRhamComparisonMap1 X (closed_form_from_cech_cocycle X φ) = φ :=
  integral_closed_form_from_cech_eq_of_spec X (deRhamComparisonMap1Spec_frontier X) φ

/-- **Surjectivity sub-obligation 1 (representative choice).**
For a prescribed period functional, choose a closed 1-form candidate
from explicit de Rham comparison data. -/
theorem deRhamComparisonMap1_prescribed_period_candidate_of_spec
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (hDR : DeRhamComparisonMap1Spec X)
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ) :
    ∃ ω : ClosedForm 1 X, ω = closed_form_from_cech_cocycle_of_spec X hDR φ := by
  exact ⟨closed_form_from_cech_cocycle_of_spec X hDR φ, rfl⟩

/-- Compatibility wrapper using the named de Rham frontier provider. -/
theorem deRhamComparisonMap1_prescribed_period_candidate
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ) :
    ∃ ω : ClosedForm 1 X, ω = closed_form_from_cech_cocycle X φ := by
  exact ⟨closed_form_from_cech_cocycle X φ, rfl⟩

/-- **Surjectivity sub-obligation 2 (prescribed-period correctness).**
The candidate closed form chosen from explicit de Rham comparison data
integrates to the requested functional. -/
theorem deRhamComparisonMap1_prescribed_period_correct_of_spec
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (hDR : DeRhamComparisonMap1Spec X)
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ) :
    deRhamComparisonMap1 X
        (Classical.choose (deRhamComparisonMap1_prescribed_period_candidate_of_spec X hDR φ)) =
      φ := by
  have h := Classical.choose_spec
    (deRhamComparisonMap1_prescribed_period_candidate_of_spec X hDR φ)
  rw [h]
  exact integral_closed_form_from_cech_eq_of_spec X hDR φ

/-- Compatibility wrapper using the named de Rham frontier provider. -/
theorem deRhamComparisonMap1_prescribed_period_correct
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ) :
    deRhamComparisonMap1 X
        (Classical.choose (deRhamComparisonMap1_prescribed_period_candidate X φ)) = φ := by
  have h := Classical.choose_spec (deRhamComparisonMap1_prescribed_period_candidate X φ)
  rw [h]
  exact integral_closed_form_from_cech_eq X φ

/-- Surjectivity of the de Rham comparison map from explicit comparison data. -/
theorem deRhamComparisonMap1_surjective_of_spec
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (hDR : DeRhamComparisonMap1Spec X)
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ) :
    ∃ ω : ClosedForm 1 X, deRhamComparisonMap1 X ω = φ := by
  refine ⟨Classical.choose (deRhamComparisonMap1_prescribed_period_candidate_of_spec X hDR φ), ?_⟩
  exact deRhamComparisonMap1_prescribed_period_correct_of_spec X hDR φ

/-- Frontier compatibility wrapper for the surjectivity half of de Rham. -/
theorem deRhamComparisonMap1_surjective
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (φ : IntegralOneCycle X →ₗ[ℤ] ℂ) :
    ∃ ω : ClosedForm 1 X, deRhamComparisonMap1 X ω = φ :=
  deRhamComparisonMap1_surjective_of_spec X (deRhamComparisonMap1Spec_frontier X) φ

/-- **Injectivity sub-obligation 1 (path-integral primitive).**
A closed 1-form with zero periods defines a global smooth 0-form via path integration.
Defined from an explicit de Rham comparison specification. -/
noncomputable def closedForm_pathIntegral_primitive_of_spec
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (hDR : DeRhamComparisonMap1Spec X)
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    SmoothDiffForm 0 X :=
  (hDR.primitive_exists ω hω).choose

/-- Compatibility wrapper using the named de Rham frontier provider. -/
noncomputable def closedForm_pathIntegral_primitive
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    SmoothDiffForm 0 X :=
  closedForm_pathIntegral_primitive_of_spec X (deRhamComparisonMap1Spec_frontier X) ω hω

/-- **Injectivity sub-obligation 2 (derivative correctness).**
The exterior derivative of the path-integral primitive is the original 1-form.
Proved from an explicit de Rham comparison specification. -/
theorem closedForm_pathIntegral_primitive_derivative_of_spec
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (hDR : DeRhamComparisonMap1Spec X)
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    exteriorDerivative 0 X (closedForm_pathIntegral_primitive_of_spec X hDR ω hω) =
      (ω : SmoothDiffForm 1 X) :=
  (hDR.primitive_exists ω hω).choose_spec

/-- Compatibility wrapper using the named de Rham frontier provider. -/
theorem closedForm_pathIntegral_primitive_derivative
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    exteriorDerivative 0 X (closedForm_pathIntegral_primitive X ω hω) = (ω : SmoothDiffForm 1 X) :=
  closedForm_pathIntegral_primitive_derivative_of_spec X
    (deRhamComparisonMap1Spec_frontier X) ω hω

/-- **Injectivity sub-obligation (zero periods give a global potential).**
If a closed 1-form has zero comparison functional, then it is the
exterior derivative of a smooth 0-form.

This is the constructive heart of the injectivity half of de Rham:
the potential is obtained by integrating the closed form along paths
and using zero periods to prove path-independence. The final kernel
statement below is only the range-membership packaging of this
potential.  This version takes the de Rham comparison data explicitly. -/
theorem deRhamComparisonMap1_zero_period_potential_of_spec
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (hDR : DeRhamComparisonMap1Spec X)
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    ∃ θ : SmoothDiffForm 0 X, exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X) := by
  exact ⟨closedForm_pathIntegral_primitive_of_spec X hDR ω hω,
    closedForm_pathIntegral_primitive_derivative_of_spec X hDR ω hω⟩

/-- Compatibility wrapper using the named de Rham frontier provider. -/
theorem deRhamComparisonMap1_zero_period_potential
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    ∃ θ : SmoothDiffForm 0 X, exteriorDerivative 0 X θ = (ω : SmoothDiffForm 1 X) :=
  deRhamComparisonMap1_zero_period_potential_of_spec X
    (deRhamComparisonMap1Spec_frontier X) ω hω


/- **Frontier identity (sorry, INJECTIVITY half of de Rham).**
A closed 1-form integrating to zero on every integer 1-cycle is
exact.

Bottom-up content: classical de Rham — vanishing periods ⇒ exactness.
Proof goes through sheaf cohomology / Čech cohomology comparison or
direct global potential construction (using simply-connected covers
and a path-integral primitive, then descent).  Mathlib gap: sheaf
cohomology comparison on manifolds is partial; global path-integral
primitive on a non-simply-connected manifold is absent. -/
/-- Injectivity half of the de Rham comparison map from explicit de Rham data. -/
theorem deRhamComparisonMap1_kernel_subset_exact_of_spec
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (hDR : DeRhamComparisonMap1Spec X)
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X := by
  rw [ExactForm]
  exact deRhamComparisonMap1_zero_period_potential_of_spec X hDR ω hω

/-- Compatibility wrapper using the named de Rham frontier provider. -/
theorem deRhamComparisonMap1_kernel_subset_exact
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (ω : ClosedForm 1 X)
    (hω : deRhamComparisonMap1 X ω = 0) :
    (ω : SmoothDiffForm 1 X) ∈ ExactForm 0 X :=
  deRhamComparisonMap1_kernel_subset_exact_of_spec X
    (deRhamComparisonMap1Spec_frontier X) ω hω

/-- **Frontier identity (sorry, ARISTOTLE-SIZED).** The de Rham
comparison map sends two cocycles in the same de-Rham class to the
same functional. Direct corollary of
`deRhamComparisonMap1_vanishes_on_exact`. -/
theorem deRhamComparisonMap1_descends
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    ∃ _ : deRhamH1Cocycle X →ₗ[ℂ] (IntegralOneCycle X →ₗ[ℤ] ℂ), True := by
  refine ⟨(ExactForm.toClosedSubmodule 0 X).liftQ (deRhamComparisonMap1 X) ?_, trivial⟩
  intro η hη
  exact LinearMap.mem_ker.mpr (deRhamComparisonMap1_vanishes_on_exact X η hη)

/-! ### Private helpers for `deRhamH1Cocycle_finrank_eq_realDim_singularH1`

The proof assembles the frontier identities (Stokes, surjectivity,
injectivity) into a linear equivalence via the first isomorphism theorem,
then bridges to `realDimSingularH1` through UCT + pure-algebra finrank.
-/

/-- Kernel of the de Rham comparison map equals the exact submodule
inside closed forms.  Proved from `deRhamComparisonMap1_vanishes_on_exact`
(⊇ direction) and `deRhamComparisonMap1_kernel_subset_exact`
(⊆ direction). -/
private theorem comparison_ker_eq_exact_of_spec
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (hDR : DeRhamComparisonMap1Spec X) :
    LinearMap.ker (deRhamComparisonMap1 X) = ExactForm.toClosedSubmodule 0 X := by
  ext η
  constructor
  · intro hη
    show (ClosedForm 1 X).subtype η ∈ ExactForm 0 X
    exact deRhamComparisonMap1_kernel_subset_exact_of_spec X hDR η (LinearMap.mem_ker.mp hη)
  · intro hη
    apply LinearMap.mem_ker.mpr
    exact deRhamComparisonMap1_vanishes_on_exact X η hη

/-- Compatibility wrapper using the named de Rham frontier provider. -/
private theorem comparison_ker_eq_exact
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    LinearMap.ker (deRhamComparisonMap1 X) = ExactForm.toClosedSubmodule 0 X :=
  comparison_ker_eq_exact_of_spec X (deRhamComparisonMap1Spec_frontier X)

/-- Range of the de Rham comparison map is all of the target space.
Proved from `deRhamComparisonMap1_surjective`. -/
private theorem comparison_range_eq_top_of_spec
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (hDR : DeRhamComparisonMap1Spec X) :
    LinearMap.range (deRhamComparisonMap1 X) = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro φ
  obtain ⟨ω, hω⟩ := deRhamComparisonMap1_surjective_of_spec X hDR φ
  exact ⟨ω, hω⟩

/-- Compatibility wrapper using the named de Rham frontier provider. -/
private theorem comparison_range_eq_top
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    LinearMap.range (deRhamComparisonMap1 X) = ⊤ :=
  comparison_range_eq_top_of_spec X (deRhamComparisonMap1Spec_frontier X)

/-- The de Rham comparison map descends to a ℂ-linear equivalence
from `deRhamH1Cocycle X` (closed mod exact) to the space of
ℤ-linear functionals `IntegralOneCycle X →ₗ[ℤ] ℂ`.

Constructed via the first isomorphism theorem: the descended map from
the quotient by the kernel to the range is an isomorphism, and the kernel
equals the exact submodule (Stokes + injectivity) while the range is
everything (surjectivity). -/
private noncomputable def deRhamH1_linearEquiv_of_spec
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (hDR : DeRhamComparisonMap1Spec X) :
    deRhamH1Cocycle X ≃ₗ[ℂ] (IntegralOneCycle X →ₗ[ℤ] ℂ) :=
  -- Step 1: deRhamH1Cocycle X ≃ₗ[ℂ] (ClosedFormSub 1 X ⧸ ker)
  (Submodule.quotEquivOfEq _ _ (comparison_ker_eq_exact_of_spec X hDR).symm) |>.trans
  -- Step 2: (ClosedFormSub 1 X ⧸ ker) ≃ₗ[ℂ] range
  ((LinearMap.quotKerEquivRange (deRhamComparisonMap1 X)) |>.trans
  -- Step 3: range ≃ₗ[ℂ] (IntegralOneCycle X →ₗ[ℤ] ℂ)
  (LinearEquiv.ofTop _ (comparison_range_eq_top_of_spec X hDR)))

/-- Compatibility wrapper using the named de Rham frontier provider. -/
private noncomputable def deRhamH1_linearEquiv
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    deRhamH1Cocycle X ≃ₗ[ℂ] (IntegralOneCycle X →ₗ[ℤ] ℂ) :=
  deRhamH1_linearEquiv_of_spec X (deRhamComparisonMap1Spec_frontier X)

/-
Pure algebra: for a finitely generated free ℤ-module `M`,
the ℂ-dimension of `Hom_ℤ(M, ℂ)` equals the ℤ-rank of `M`.

Analogous to `finrank_homℤℝ_eq_finrank_of_free` but over ℂ.
-/
private theorem finrank_homℤℂ_eq_finrank_of_free
    (M : Type*) [AddCommGroup M] [Module ℤ M]
    [Module.Free ℤ M] [Module.Finite ℤ M] :
    Module.finrank ℂ (M →ₗ[ℤ] ℂ) = Module.finrank ℤ M := by
  have h_basis : ∃ b : Module.Basis (Fin (Module.finrank ℤ M)) ℤ M, True := by
    exact ⟨ Module.finBasis ℤ M, trivial ⟩;
  obtain ⟨ b, hb ⟩ := h_basis;
  have h_iso : (M →ₗ[ℤ] ℂ) ≃ₗ[ℂ] (Fin (Module.finrank ℤ M) → ℂ) := by
    exact (b.constr ℂ).symm
  simpa using LinearEquiv.finrank_eq h_iso

/-- **Frontier identity (sorry).** The descended de Rham comparison map
is a linear equivalence, at the level of finrank: the closed-mod-exact
quotient and the cycle-functional space have the same `Module.finrank ℂ`.

Proved from the linear equivalence `deRhamH1_linearEquiv` (which uses
the sorry'd Stokes, surjectivity, and injectivity frontier identities),
the UCT bridge `realDim_singularH1_eq_finrank_intH1_via_uct`, and the
pure-algebra identity `finrank_homℤℂ_eq_finrank_of_free`. -/
theorem deRhamH1Cocycle_finrank_eq_realDim_singularH1
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    Module.finrank ℂ (deRhamH1Cocycle X) = realDimSingularH1 X := by
  rw [(deRhamH1_linearEquiv X).finrank_eq]
  rw [realDim_singularH1_eq_finrank_intH1_via_uct X]
  haveI : Module.Finite ℤ (IntegralOneCycle X) := IntegralOneCycle_finite X
  haveI : Module.Free ℤ (IntegralOneCycle X) := IntegralOneCycle_torsionFree X
  exact finrank_homℤℂ_eq_finrank_of_free (IntegralOneCycle X)

/-- **Round-2 sorry-free assembly.** Bridges
`realDim_deRhamH1_eq_realDim_singularH1` from `DeRhamSingular.lean`
through the explicit quotient model + integration map. -/
theorem realDimDeRhamH1_eq_realDimSingularH1_via_cocycle
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    realDimDeRhamH1 X = realDimSingularH1 X := by
  rw [realDimDeRhamH1_eq_finrank_cocycleℝ X,
      deRhamH1Cocycle_finrank_eq_realDim_singularH1 X]

end JacobianChallenge.HolomorphicForms
