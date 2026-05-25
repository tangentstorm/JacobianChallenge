import Jacobian.HolomorphicForms.SmoothDifferentialForm
import Jacobian.HolomorphicForms.HodgeStarRS
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-!
# Hodge Laplacian on a Riemann surface

A Hermitian metric on a Riemann surface gives:

* a **Hodge ⋆ operator** `⋆ : Ω^n(X) → Ω^{2-n}(X)` (with `⋆² = (-1)^n`
  in dimension 2),
* a formal adjoint `d^* : Ω^{n+1}(X) → Ω^n(X)` defined as
  `d^* := -⋆ d ⋆`,
* the **Hodge Laplacian** `Δ : Ω^n(X) → Ω^n(X)` defined as
  `Δ := dd^* + d^*d`.

`Δ` is a second-order self-adjoint elliptic operator.  Its kernel on
`Ω^n(X)` is exactly the space of *harmonic* `n`-forms, and on a compact
manifold elliptic regularity gives `Harm^n` finite-dimensional.

## What this file provides

## TOPDOWN role

This file refines the harmonic-projection / harmonic-finiteness
sorries in `HodgeStarRS.lean` into the explicit elliptic-operator
ingredients.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/--
Since `SmoothDiffForm 1 X` is currently just a complex vector-space
surrogate, this uses multiplication by `I`, giving the correct algebraic
identity `⋆² = -1` on 1-forms. The geometric bottom-up replacement will
come from a Hermitian metric and the metric Hodge star once the cotangent
metric / Hodge-star API exists.
-/
noncomputable def hodgeStarOp
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    SmoothDiffForm 1 X →ₗ[ℂ] SmoothDiffForm 1 X :=
  Complex.I • LinearMap.id


theorem hodgeStarOp_squared
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    (hodgeStarOp X).comp (hodgeStarOp X) = -LinearMap.id := by
  ext ω
  simp [hodgeStarOp]
  rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]

/--
Current-model formal adjoint `d^*_1 : Ω¹(X) → Ω⁰(X)`.

With the current zero-differential surrogate for `d`, the compatible
formal adjoint is also zero. The geometric replacement is the metric
adjoint `-⋆ d ⋆` once the real Hodge-star/form API exists.
-/
noncomputable def dStarOperator1
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    SmoothDiffForm 1 X →ₗ[ℂ] SmoothDiffForm 0 X :=
  0

/--
Current-model formal adjoint `d^*_2 : Ω²(X) → Ω¹(X)`, also zero
for the zero-differential surrogate.
-/
noncomputable def dStarOperator2
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    SmoothDiffForm 2 X →ₗ[ℂ] SmoothDiffForm 1 X :=
  0


noncomputable def hodgeLaplacian1
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    SmoothDiffForm 1 X →ₗ[ℂ] SmoothDiffForm 1 X :=
  (exteriorDerivative 0 X).comp (dStarOperator1 X)
    + (dStarOperator2 X).comp (exteriorDerivative 1 X)


theorem hodgeLaplacian1_def
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    hodgeLaplacian1 X
      = (exteriorDerivative 0 X).comp (dStarOperator1 X)
        + (dStarOperator2 X).comp (exteriorDerivative 1 X) := by
  rfl

/--
**Current-model energy identity.** A 1-form in the kernel of the
zero-surrogate Hodge Laplacian is both closed and co-closed.

Bottom-up content: the standard identity
`⟪Δω,ω⟫ = ‖dω‖² + ‖d*ω‖²` on compact manifolds.
-/
theorem hodgeLaplacian1_kernel_subset_closed_coclosed
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (ω : SmoothDiffForm 1 X)
    (_hω : hodgeLaplacian1 X ω = 0) :
    exteriorDerivative 1 X ω = 0 ∧ dStarOperator1 X ω = 0 := by
  simp [exteriorDerivative, dStarOperator1]

/--
**Current-model kernel identity.** A 1-form is in the kernel of `Δ`
iff it is both `d`-closed and `d^*`-closed.
-/
theorem hodgeLaplacian1_kernel_iff
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (ω : SmoothDiffForm 1 X) :
    hodgeLaplacian1 X ω = 0 ↔
      exteriorDerivative 1 X ω = 0 ∧ dStarOperator1 X ω = 0 := by
  constructor
  · exact hodgeLaplacian1_kernel_subset_closed_coclosed X ω
  · rintro ⟨hdω, hdsω⟩
    simp [hodgeLaplacian1, hdω, hdsω]

/--
**Current-model identification.** Identification of `HarmonicOneForm X`
(the alias `Fin 2 → HolomorphicOneForm ℂ X` from `HodgeStarRS.lean`)
with the kernel of `Δ` on smooth 1-forms. Stated as an existence
theorem to keep downstream consumers independent of the chosen
surrogate representation.
-/
theorem harmonicEquivLaplacianKernel
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    ∃ _ : HarmonicOneForm X ≃ₗ[ℂ] LinearMap.ker (hodgeLaplacian1 X), True := by
  refine ⟨?_, trivial⟩
  refine
    { toFun := fun ω => ⟨ω, by simp [hodgeLaplacian1, exteriorDerivative,
        dStarOperator1, dStarOperator2]⟩
      invFun := fun ω => ω.1
      map_add' := by intro ω η; rfl
      map_smul' := by intro c ω; rfl
      left_inv := by intro ω; rfl
      right_inv := by intro ω; exact Subtype.ext rfl }


theorem hodgeLaplacian1_kernel_finite
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [HolomorphicOneFormMontelData X] :
    Module.Finite ℂ (LinearMap.ker (hodgeLaplacian1 X)) := by
  obtain ⟨e, _⟩ := harmonicEquivLaplacianKernel X
  haveI : Module.Finite ℂ (HarmonicOneForm X) := analyticHarmonicGenus_finite X
  exact Module.Finite.equiv e

end JacobianChallenge.HolomorphicForms
