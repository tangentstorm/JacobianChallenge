import Jacobian.HolomorphicForms.SmoothDifferentialForm
import Jacobian.HolomorphicForms.HodgeStarRS

/-!
# Hodge Laplacian on a Riemann surface (frontier API)

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

## What this file provides (round 2 refinement)

* `hodgeStar n X` — opaque ℂ-linear map `Ω^n(X) → Ω^{2-n}(X)`.
* `hodgeStar_squared` — frontier identity (sorry).
* `dStarOperator n X` — opaque adjoint `d^* : Ω^{n+1} → Ω^n`.
* `hodgeLaplacian n X` — opaque Laplacian `Δ : Ω^n → Ω^n`.
* `harmonic_iff_kernel_laplacian` — frontier identity (sorry):
  harmonic forms = kernel of Δ.
* `laplacian_kernel_finite` — frontier identity (sorry):
  kernel of Δ is finite-dimensional.

## TOPDOWN role

This file refines the harmonic-projection / harmonic-finiteness
sorries in `HodgeStarRS.lean` into the explicit elliptic-operator
ingredients.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/-- **Frontier opaque.** The Hodge ⋆ operator `Ω^n(X) → Ω^{2-n}(X)`.
For a 1-form on a Riemann surface (real dim 2) it is the operator `⋆`
satisfying `⋆² = -1` (the conformal-rotation `dz ↦ -i dz̄` /
`dz̄ ↦ i dz`).

Bottom-up content: choose a Hermitian metric (existence by partition
of unity); ⋆ is the metric Hodge ⋆.  Mathlib gap: cotangent metric +
Hodge ⋆ both absent. -/
noncomputable opaque hodgeStarOp
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    SmoothDiffForm 1 X →ₗ[ℂ] SmoothDiffForm 1 X

/-- **Frontier identity (sorry).** `⋆² = -1` on 1-forms in real
dimension 2 (a Riemann surface). -/
theorem hodgeStarOp_squared
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    (hodgeStarOp X).comp (hodgeStarOp X) = -LinearMap.id := by
  sorry

/-- **Frontier opaque.** The formal adjoint `d^*_1 : Ω¹(X) → Ω⁰(X)` of
`d_0 : Ω⁰ → Ω¹`. Classically `d^* := -⋆ d ⋆` on a Riemann surface. -/
noncomputable opaque dStarOperator1
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    SmoothDiffForm 1 X →ₗ[ℂ] SmoothDiffForm 0 X

/-- **Frontier opaque.** The formal adjoint `d^*_2 : Ω²(X) → Ω¹(X)` of
`d_1 : Ω¹ → Ω²`. -/
noncomputable opaque dStarOperator2
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    SmoothDiffForm 2 X →ₗ[ℂ] SmoothDiffForm 1 X

/-- **Frontier opaque.** The Hodge Laplacian on 1-forms,
`Δ := d_0 ∘ d^*_1 + d^*_2 ∘ d_1 : Ω¹ → Ω¹`. -/
noncomputable def hodgeLaplacian1
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    SmoothDiffForm 1 X →ₗ[ℂ] SmoothDiffForm 1 X :=
  (exteriorDerivative 0 X).comp (dStarOperator1 X)
    + (dStarOperator2 X).comp (exteriorDerivative 1 X)

/-- **Frontier identity (sorry).** `Δ` is the sum of `d_0 ∘ d^*_1` and
`d^*_2 ∘ d_1` applied to 1-forms. Definition-shaped frontier theorem. -/
theorem hodgeLaplacian1_def
    (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    hodgeLaplacian1 X
      = (exteriorDerivative 0 X).comp (dStarOperator1 X)
        + (dStarOperator2 X).comp (exteriorDerivative 1 X) := by
  rfl

/-- **Frontier identity (sorry).** A 1-form is in the kernel of `Δ` iff
it is both `d`-closed and `d^*`-closed.

Bottom-up content: `(Δω, ω) = ‖dω‖² + ‖d^*ω‖²` for the L² inner
product; `Δω = 0` ⇒ both norms vanish ⇒ both `d`-closed and
`d^*`-closed. The reverse direction is direct from the definition.
Mathlib gap: L² inner product on forms, integration by parts on
manifolds, all absent in v4.28.0. -/
theorem hodgeLaplacian1_kernel_iff
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (ω : SmoothDiffForm 1 X) :
    hodgeLaplacian1 X ω = 0 ↔
      exteriorDerivative 1 X ω = 0 ∧ dStarOperator1 X ω = 0 := by
  sorry

/-- **Frontier theorem (sorry).** Identification of `HarmonicOneForm X`
(the alias `Fin 2 → HolomorphicOneForm ℂ X` from `HodgeStarRS.lean`)
with the kernel of `Δ` on smooth 1-forms. Stated as an existence
theorem to avoid the `Nonempty` synthesis required by `opaque`
declarations on `LinearEquiv`-typed bodies. -/
theorem harmonicEquivLaplacianKernel
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    ∃ _ : HarmonicOneForm X ≃ₗ[ℂ] LinearMap.ker (hodgeLaplacian1 X), True := by
  sorry

/-- **Frontier identity (sorry, ELLIPTIC REGULARITY).** The kernel of
the Hodge Laplacian on 1-forms is finite-dimensional over ℂ on a
compact connected Riemann surface.

Bottom-up content: Δ is a second-order elliptic operator on a compact
manifold; Gårding's inequality + Rellich–Kondrachov compact embedding
gives kernel finite-dimensional.  Mathlib gap: Sobolev spaces on
manifolds + compact embedding + elliptic regularity; partial pieces
exist but the Laplacian on forms requires the form apparatus first. -/
theorem hodgeLaplacian1_kernel_finite
    (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Module.Finite ℂ (LinearMap.ker (hodgeLaplacian1 X)) := by
  sorry

end JacobianChallenge.HolomorphicForms
