import Jacobian.TraceDegree.PullbackFormsLinearMapConst

/-!
# Vector-apply form of pullback along a constant map (bundled)

Pointwise apply form: applying the bundled pullback along a constant
map at a point and a tangent vector gives 0.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

/-- Vector-apply form of the bundled constant pullback: zero. -/
@[simp] theorem pullbackFormsLinearMap_const_apply_vec
    (y : Y) (η : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsLinearMap (Function.const X y) η x v = 0 := by
  rw [pullbackFormsLinearMap_const_apply]; rfl

end JacobianChallenge.TraceDegree
