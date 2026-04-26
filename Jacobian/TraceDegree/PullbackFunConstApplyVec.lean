import Jacobian.TraceDegree.PullbackFunConst

/-!
# Pointwise vector apply form of `pullbackFormsFun_const`

`pullbackFormsFun (Function.const X y) η x v = 0`: applying the
pullback along a constant map at a point and a tangent vector is
zero.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

set_option linter.unusedSectionVars false in
/-- Pointwise vector-apply form: pullback along a constant map at a
point and tangent vector is zero. -/
@[simp] theorem pullbackFormsFun_const_apply
    (y : Y) (η : HolomorphicOneForm E Y) (x : X) (v : E) :
    pullbackFormsFun (Function.const X y) η x v = 0 := by
  rw [pullbackFormsFun_const]; rfl

end JacobianChallenge.TraceDegree
