import Jacobian.HolomorphicForms.ToFunApplyVec

/-!
# Pointwise vector-evaluation as a `LinearMap`

For fixed `x : X` and `v : E`, the assignment `η ↦ η.toFun x v` is
ℂ-linear in the form `η`. Bundles this as
`HolomorphicOneForm.evalLinearMap x v : HolomorphicOneForm E X →ₗ[ℂ] ℂ`,
the building block of period pairing.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
Pointwise vector-evaluation of a holomorphic 1-form, packaged as a
ℂ-linear map.
-/
noncomputable def evalLinearMap (x : X) (v : E) :
    HolomorphicOneForm E X →ₗ[ℂ] ℂ where
  toFun η := η.toFun x v
  map_add' η ζ := by simp
  map_smul' k η := by simp

@[simp] theorem evalLinearMap_apply
    (x : X) (v : E) (η : HolomorphicOneForm E X) :
    evalLinearMap x v η = η.toFun x v := rfl

@[simp] theorem evalLinearMap_zero
    (x : X) (v : E) :
    evalLinearMap (E := E) (X := X) x v 0 = 0 :=
  (evalLinearMap x v).map_zero

theorem evalLinearMap_add
    (x : X) (v : E) (η ζ : HolomorphicOneForm E X) :
    evalLinearMap x v (η + ζ) = evalLinearMap x v η + evalLinearMap x v ζ :=
  (evalLinearMap x v).map_add η ζ

end JacobianChallenge.HolomorphicForms
