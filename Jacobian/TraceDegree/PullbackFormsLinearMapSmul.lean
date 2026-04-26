import Jacobian.TraceDegree.PullbackFormsLinearMap

/-!
# Scalar-multiplication lemma for `pullbackFormsLinearMap`
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

/-- `pullbackFormsLinearMap` distributes over scalar multiplication. -/
@[simp] theorem pullbackFormsLinearMap_smul
    (f : X → Y) (k : ℂ) (η : HolomorphicOneForm E Y) :
    pullbackFormsLinearMap f (k • η) = k • pullbackFormsLinearMap f η :=
  LinearMap.map_smul (pullbackFormsLinearMap f) k η

end JacobianChallenge.TraceDegree
