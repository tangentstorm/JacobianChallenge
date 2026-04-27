import Jacobian.HolomorphicForms.EvalLinearMap

/-!
# Linearity of `evalLinearMap` in the tangent-vector slot

`evalLinearMap` is parameterised by `(x, v)` and returns a ℂ-linear
map in the form slot. Holding `(x, η)` fixed, it is also a continuous
ℂ-linear map in the tangent-vector slot — this is just `η.toFun x`,
applied as a `ContinuousLinearMap`. This file exposes that linearity
as named simp lemmas, mirroring the form-side `EvalLinearMapApi`.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

@[simp] theorem evalLinearMap_zero_vec
    (x : X) (η : HolomorphicOneForm E X) :
    evalLinearMap x (0 : E) η = 0 := by
  rw [evalLinearMap_apply]
  exact (η.toFun x).map_zero

@[simp] theorem evalLinearMap_add_vec
    (x : X) (v w : E) (η : HolomorphicOneForm E X) :
    evalLinearMap x (v + w) η = evalLinearMap x v η + evalLinearMap x w η := by
  rw [evalLinearMap_apply, evalLinearMap_apply, evalLinearMap_apply]
  exact (η.toFun x).map_add v w

@[simp] theorem evalLinearMap_smul_vec
    (x : X) (k : ℂ) (v : E) (η : HolomorphicOneForm E X) :
    evalLinearMap x (k • v) η = k • evalLinearMap x v η := by
  rw [evalLinearMap_apply, evalLinearMap_apply]
  exact (η.toFun x).map_smul k v

@[simp] theorem evalLinearMap_neg_vec
    (x : X) (v : E) (η : HolomorphicOneForm E X) :
    evalLinearMap x (-v) η = -evalLinearMap x v η := by
  rw [evalLinearMap_apply, evalLinearMap_apply]
  exact (η.toFun x).map_neg v

end JacobianChallenge.HolomorphicForms
