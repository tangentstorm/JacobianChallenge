import Jacobian.TraceDegree.PullbackFormsLinearMap
import Jacobian.TraceDegree.PullbackFunConst

/-!
# Pullback linear map along a constant map is zero

Combines the bundled `pullbackFormsLinearMap` with the unbundled
`pullbackFormsFun_const` to show the linear-map version also sends
every form to zero.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

/--
The bundled pullback `LinearMap` along a constant map sends
every form to the zero function.
-/
@[simp] theorem pullbackFormsLinearMap_const_apply
    (y : Y) (η : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap (Function.const X y) η = 0 :=
  pullbackFormsFun_const y η

end JacobianChallenge.TraceDegree
