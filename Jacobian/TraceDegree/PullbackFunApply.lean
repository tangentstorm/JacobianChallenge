import Jacobian.TraceDegree.PullbackFun

/-!
# Definitional unfolding of `pullbackFormsFun`

A `rfl`-style simp lemma exposing the chain-rule formula
`(f^*η)_x = η_{f x} ∘ mfderiv f x`.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

/-- The pullback function evaluated at a point is the chain-rule
formula `(f^*η)_x = η_{f x} ∘ mfderiv f x`. -/
@[simp] theorem pullbackFormsFun_apply
    (f : X → Y) (η : HolomorphicOneForm E Y) (x : X) :
    pullbackFormsFun f η x =
      (η.toFun (f x)).comp
        (mfderiv (modelWithCornersSelf ℂ E)
                 (modelWithCornersSelf ℂ E) f x) := rfl

end JacobianChallenge.TraceDegree
