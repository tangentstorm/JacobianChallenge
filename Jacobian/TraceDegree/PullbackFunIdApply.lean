import Jacobian.TraceDegree.PullbackFunId

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Pullback along the identity map evaluated at a point. -/
@[simp] theorem pullbackFormsFun_id_apply
    (η : HolomorphicOneForm E X) (x : X) :
    pullbackFormsFun (id : X → X) η x = η.toFun x := by
  rw [pullbackFormsFun_id]

end JacobianChallenge.TraceDegree
