import Jacobian.TraceDegree.PullbackFunIdApply

/-!
# Vector-apply form of `pullbackFormsFun_id`

Pointwise apply form of `pullbackFormsFun_id` evaluated on a tangent
vector: `pullbackFormsFun id η x v = η.toFun x v`.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Vector-apply form of identity pullback: applied at a point and a
tangent vector gives `η.toFun x v`. -/
@[simp] theorem pullbackFormsFun_id_apply_vec
    (η : HolomorphicOneForm E X) (x : X) (v : E) :
    pullbackFormsFun (id : X → X) η x v = η.toFun x v := by
  rw [pullbackFormsFun_id_apply]
  rfl

end JacobianChallenge.TraceDegree
