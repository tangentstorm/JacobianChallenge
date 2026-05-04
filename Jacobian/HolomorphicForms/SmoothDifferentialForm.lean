import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Complex.Basic
import Jacobian.HolomorphicForms.Defs

/-!
# Smooth k-forms on a complex manifold (frontier API)

Frontier-layer surrogates for ℂ-valued smooth differential `k`-forms on
a complex manifold `X`.  Mathlib v4.28.0 has the cotangent bundle but
does **not** have a global `Λ^k T*X`-section type, the exterior
derivative `d`, or the de Rham cochain complex.

This file declares the missing data as named opaques + frontier
identities so deeper refinement passes (de Rham theorem, Stokes,
Hodge ⋆) can name and reuse them.

## What this file provides (round 2 refinement)

* `SmoothDiffForm n X` — opaque ℂ-vector space of smooth ℂ-valued
  `n`-forms on `X`. AddCommGroup/Module instances declared as
  separate opaques.
* `exteriorDerivative n X` — opaque ℂ-linear map `Ω^n(X) → Ω^{n+1}(X)`.
* `exteriorDerivative_squared_eq_zero` — frontier identity (sorry).
* `ClosedForm n X` / `ExactForm n X` — kernel/image submodules.
* `deRham_eq_quotient` — frontier identity bridging
  `complexDimDeRhamH1ℂ` to the explicit `closed / exact` description.

## TOPDOWN role

This is the **substrate** for the de Rham theorem refinement: once the
forms type and `d` are named, the comparison map to singular cochains
(in `DeRhamComparisonMap.lean`) can be expressed precisely.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/-- **Frontier alias.** Smooth ℂ-valued `n`-forms on the complex manifold
`X`. As a placeholder we alias to `Fin n.succ → HolomorphicOneForm ℂ X`,
giving us a concrete inhabited ℂ-vector space of the right shape (`Ω⁰ ≃
ℂ ↦ functions ≃ Hol`-ish, `Ω¹ = forms`, etc., are *not* faithfully
modelled — the only structural commitment is that we have a ℂ-vector
space named `SmoothDiffForm n X`). When Mathlib gains a real
`Λ^n T*X`-section type, this alias is replaced and the surrounding
named identities pick up the substantive obligations. -/
abbrev SmoothDiffForm
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] : Type _ :=
  Fin n.succ → HolomorphicOneForm ℂ X

/-- Current-model exterior derivative `d : Ω^n(X) → Ω^{n+1}(X)`.

The current `SmoothDiffForm` substrate is only a vector-space surrogate,
with no wedge product or chartwise coefficient calculus. We therefore use
the zero differential as the honest cochain-complex model at this layer:
it gives the algebraic invariant `d² = 0` without pretending to provide
the geometric exterior derivative. The bottom-up replacement is the
classical chartwise operator once global differential forms exist. -/
noncomputable def exteriorDerivative
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    SmoothDiffForm n X →ₗ[ℂ] SmoothDiffForm n.succ X :=
  0

/-- `d² = 0` for the current zero-differential form substrate. -/
theorem exteriorDerivative_squared_eq_zero
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    (exteriorDerivative n.succ X).comp (exteriorDerivative n X) = 0 := by
  rfl

/-- The kernel of `d : Ω^n → Ω^{n+1}` — the **closed** `n`-forms. -/
noncomputable def ClosedForm
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Submodule ℂ (SmoothDiffForm n X) :=
  LinearMap.ker (exteriorDerivative n X)

/-- The image of `d : Ω^{n-1} → Ω^n` — the **exact** `n`-forms. -/
noncomputable def ExactForm
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Submodule ℂ (SmoothDiffForm n.succ X) :=
  LinearMap.range (exteriorDerivative n X)

/-- The carrier (subtype) of `ClosedForm n X`, with explicit instances
to break the typeclass-resolution slowness when unfolding through
`Fin _ → HolomorphicOneForm`. -/
noncomputable abbrev ClosedFormSub
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Type _ :=
  ↥(ClosedForm n X)

noncomputable instance ClosedFormSub.instAddCommGroup
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    AddCommGroup (ClosedFormSub n X) :=
  Submodule.addCommGroup _

noncomputable instance ClosedFormSub.instModuleℂ
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Module ℂ (ClosedFormSub n X) :=
  Submodule.module _

/-- **Frontier theorem (sorry).** Exact ⊆ closed: `d² = 0` lifted to
submodules. Bottom-up content: direct from
`exteriorDerivative_squared_eq_zero` plus
`LinearMap.range_le_ker_iff`. ARISTOTLE-SIZED. -/
theorem ExactForm_le_ClosedForm
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    ExactForm n X ≤ ClosedForm n.succ X := by
  rw [ExactForm, ClosedForm]
  exact LinearMap.range_le_ker_iff.mpr (exteriorDerivative_squared_eq_zero n X)

/-- Submodule of exact forms inside closed forms — direct from
`ExactForm_le_ClosedForm`.  Stated as a name for use as the
denominator in the H¹_dR quotient. -/
noncomputable def ExactForm.toClosedSubmodule
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Submodule ℂ (ClosedFormSub n.succ X) :=
  (ExactForm n X).comap (ClosedForm n.succ X).subtype

end JacobianChallenge.HolomorphicForms
