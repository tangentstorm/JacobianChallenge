import Jacobian.HolomorphicForms.CotangentBundle
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection

/-!
# Holomorphic 1-forms on a complex manifold

Defines `HolomorphicOneForm X` as the type of `ContMDiff` analytic
sections of the cotangent bundle of a complex manifold `X` modeled on
a complex normed space `E`.

The algebraic structure (`AddCommGroup`, `Module ℂ`) is inherited for
free from `ContMDiffSection`.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/--
A holomorphic 1-form on a complex manifold `X` is an analytic
(`ContMDiff` with `n = ⊤`) section of the cotangent bundle.
-/
abbrev HolomorphicOneForm
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Type*) [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X] :
    Type _ :=
  Cₛ^(⊤ : WithTop ℕ∞)⟮modelWithCornersSelf ℂ E;
    CotangentModelFiber E, CotangentSpace E X⟯

/-- Sanity check: `AddCommGroup` is inherited from `ContMDiffSection`. -/
noncomputable example
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Type*) [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X] :
    AddCommGroup (HolomorphicOneForm E X) :=
  inferInstance

/-- Sanity check: `Module ℂ` is inherited from `ContMDiffSection`. -/
noncomputable example
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (X : Type*) [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X] :
    Module ℂ (HolomorphicOneForm E X) :=
  inferInstance

end JacobianChallenge.HolomorphicForms
