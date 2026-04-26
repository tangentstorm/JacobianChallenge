import Jacobian.TraceDegree.PullbackFun

/-!
# Tangent-vector application of `pullbackFormsFun`

Unfolds `pullbackFormsFun f η x v` to the explicit chain-rule formula
`η_{f x} (mfderiv f x v)`, by composing `pullbackFormsFun_apply` with
`ContinuousLinearMap.comp_apply`.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

/-- Applying the pullback function at a point and then at a tangent
vector gives the chain-rule formula
`(f^*η)_x v = η_{f x} (mfderiv f x v)`. -/
@[simp] theorem pullbackFormsFun_apply_apply
    (f : X → Y) (η : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsFun f η x v =
      η.toFun (f x) (mfderiv (modelWithCornersSelf ℂ E)
                             (modelWithCornersSelf ℂ E) f x v) := rfl

end JacobianChallenge.TraceDegree
