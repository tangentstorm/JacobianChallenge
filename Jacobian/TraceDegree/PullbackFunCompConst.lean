import Jacobian.TraceDegree.PullbackFunConst

/-!
# Pullback along a map that factors through a point

`pullbackFormsFun (f ∘ Function.const X x₀) η = 0` — pullback along
any map of the form `f ∘ const x₀` (i.e., that factors through a
single point) is zero, because such a composition is itself a
constant map.

Direct corollary of `pullbackFormsFun_const`.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y Z : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [TopologicalSpace Z] [ChartedSpace E Z]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Z]

set_option linter.unusedSectionVars false in
/-- Pullback along `f ∘ const x₀` is zero (the composition is itself
a constant map, namely `const X (f x₀)`). -/
@[simp] theorem pullbackFormsFun_comp_const
    (f : Y → Z) (x₀ : Y) (η : HolomorphicOneForm E Z) :
    pullbackFormsFun (f ∘ Function.const X x₀) η = 0 := by
  show pullbackFormsFun (Function.const X (f x₀)) η = 0
  exact pullbackFormsFun_const (f x₀) η

end JacobianChallenge.TraceDegree
