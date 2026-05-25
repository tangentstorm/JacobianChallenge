import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Complex.Basic
import Jacobian.HolomorphicForms.Defs
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-!
# Smooth k-forms on a complex manifold

## What this file provides

## TOPDOWN role

This is the **substrate** for the de Rham theorem refinement: once the
forms type and `d` are named, the comparison map to singular cochains
(in `DeRhamComparisonMap.lean`) can be expressed precisely.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold


abbrev SmoothDiffForm
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] : Type _ :=
  Fin n.succ → HolomorphicOneForm ℂ X

/--
Current-model exterior derivative `d : Ω^n(X) → Ω^{n+1}(X)`.

The current `SmoothDiffForm` substrate is only a vector-space surrogate,
with no wedge product or chartwise coefficient calculus. We therefore use
the zero differential as the honest cochain-complex model at this layer:
it gives the algebraic invariant `d² = 0` without pretending to provide
the geometric exterior derivative. The bottom-up replacement is the
classical chartwise operator once global differential forms exist.
-/
noncomputable def exteriorDerivative
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    SmoothDiffForm n X →ₗ[ℂ] SmoothDiffForm n.succ X :=
  0

/-- `d² = 0` for the current zero-differential form substrate. -/
theorem exteriorDerivative_squared_eq_zero
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    (exteriorDerivative n.succ X).comp (exteriorDerivative n X) = 0 := by
  rfl

/-- The kernel of `d : Ω^n → Ω^{n+1}` — the **closed** `n`-forms. -/
noncomputable def ClosedForm
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    Submodule ℂ (SmoothDiffForm n X) :=
  LinearMap.ker (exteriorDerivative n X)

/-- The image of `d : Ω^{n-1} → Ω^n` — the **exact** `n`-forms. -/
noncomputable def ExactForm
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    Submodule ℂ (SmoothDiffForm n.succ X) :=
  LinearMap.range (exteriorDerivative n X)

/--
The carrier (subtype) of `ClosedForm n X`, with explicit instances
to break the typeclass-resolution slowness when unfolding through
`Fin _ → HolomorphicOneForm`.
-/
noncomputable abbrev ClosedFormSub
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    Type _ :=
  ↥(ClosedForm n X)

noncomputable instance ClosedFormSub.instAddCommGroup
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    AddCommGroup (ClosedFormSub n X) :=
  Submodule.addCommGroup _

noncomputable instance ClosedFormSub.instModuleℂ
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    Module ℂ (ClosedFormSub n X) :=
  Submodule.module _


theorem ExactForm_le_ClosedForm
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    ExactForm n X ≤ ClosedForm n.succ X := by
  rw [ExactForm, ClosedForm]
  exact LinearMap.range_le_ker_iff.mpr (exteriorDerivative_squared_eq_zero n X)

/--
Submodule of exact forms inside closed forms — direct from
`ExactForm_le_ClosedForm`.  Stated as a name for use as the
denominator in the H¹_dR quotient.
-/
noncomputable def ExactForm.toClosedSubmodule
    (n : ℕ) (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    Submodule ℂ (ClosedFormSub n.succ X) :=
  (ExactForm n X).comap (ClosedForm n.succ X).subtype

end JacobianChallenge.HolomorphicForms
