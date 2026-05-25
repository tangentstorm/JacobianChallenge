import Jacobian.TraceDegree.PullbackFunConst

/-!
# Pullback along the post-composition of a constant map

`pullbackFormsFun (Function.const Y z ∘ f) η = 0` — the composition
of a constant map with anything is itself constant, so the pullback
vanishes. Symmetric counterpart of `pullbackFormsFun_comp_const`.
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
/--
Pullback along `Function.const Y z ∘ f` is zero. The composition
is itself constant (`Function.const X z`), so this reduces to
`pullbackFormsFun_const`.
-/
@[simp] theorem pullbackFormsFun_const_comp
    (z : Z) (f : X → Y) (η : HolomorphicOneForm E Z) :
    pullbackFormsFun (Function.const Y z ∘ f) η = 0 := by
  show pullbackFormsFun (Function.const X z) η = 0
  exact pullbackFormsFun_const z η

end JacobianChallenge.TraceDegree
