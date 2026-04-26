import Jacobian.TraceDegree.PullbackFormsLinearMap

/-!
# Pointwise application of `pullbackFormsLinearMap`

Gives the explicit pointwise form: applying the bundled `LinearMap` to a
form and then evaluating at a point equals `pullbackFormsFun f η x`.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

/-- Applying the bundled pullback `LinearMap` at a point. -/
@[simp] theorem pullbackFormsLinearMap_apply_at
    (f : X → Y) (η : HolomorphicOneForm E Y) (x : X) :
    pullbackFormsLinearMap f η x = pullbackFormsFun f η x := rfl

/-- Applying the bundled pullback `LinearMap` at a point and then at a
tangent vector gives the chain-rule formula. -/
@[simp] theorem pullbackFormsLinearMap_apply_vec
    (f : X → Y) (η : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap f η x v =
      η.toFun (f x) (mfderiv (modelWithCornersSelf ℂ E)
                             (modelWithCornersSelf ℂ E) f x v) := rfl

end JacobianChallenge.TraceDegree
