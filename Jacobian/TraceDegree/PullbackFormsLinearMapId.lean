import Jacobian.TraceDegree.PullbackFormsLinearMap
import Jacobian.TraceDegree.PullbackFunId

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- The bundled pullback along the identity map equals the form's
underlying function. -/
@[simp] theorem pullbackFormsLinearMap_id_apply
    (η : HolomorphicOneForm E X) :
    pullbackFormsLinearMap (id : X → X) η = η.toFun :=
  pullbackFormsFun_id η

end JacobianChallenge.TraceDegree
