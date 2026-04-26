import Jacobian.TraceDegree.PullbackFormsLinearMapId

/-!
# Vector-apply form of `pullbackFormsLinearMap_id`

Bundled-LinearMap-level analogue of `pullbackFormsFun_id_apply_vec`:
applying the identity-pullback at a point and a tangent vector
gives `η.toFun x v` directly.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Bundled vector-apply form of identity pullback. -/
@[simp] theorem pullbackFormsLinearMap_id_apply_vec
    (η : HolomorphicOneForm E X) (x : X) (v : E) :
    pullbackFormsLinearMap (id : X → X) η x v = η.toFun x v := by
  rw [pullbackFormsLinearMap_id_apply]; rfl

end JacobianChallenge.TraceDegree
