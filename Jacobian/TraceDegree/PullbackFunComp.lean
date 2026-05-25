import Jacobian.TraceDegree.PullbackFun

/-!
# Pullback along a composition (pointwise chain rule)

`pullbackFormsFun (g ∘ f) η x` factors through `mfderiv g (f x)` and
`mfderiv f x` via the chain rule for `mfderiv`. Conditional on
`MDifferentiableAt` for both `g` (at `f x`) and `f` (at `x`).
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
Pullback along a composition factors via the chain rule for
`mfderiv`. Conditional on `MDifferentiableAt` for both maps.
-/
theorem pullbackFormsFun_comp_apply
    (f : X → Y) (g : Y → Z) (η : HolomorphicOneForm E Z) (x : X)
    (hg : MDifferentiableAt (modelWithCornersSelf ℂ E)
                            (modelWithCornersSelf ℂ E) g (f x))
    (hf : MDifferentiableAt (modelWithCornersSelf ℂ E)
                            (modelWithCornersSelf ℂ E) f x) :
    pullbackFormsFun (g ∘ f) η x =
      ((η.toFun (g (f x))).comp
        (mfderiv (modelWithCornersSelf ℂ E)
                 (modelWithCornersSelf ℂ E) g (f x))).comp
        (mfderiv (modelWithCornersSelf ℂ E)
                 (modelWithCornersSelf ℂ E) f x) := by
  show (η.toFun ((g ∘ f) x)).comp
        (mfderiv (modelWithCornersSelf ℂ E)
                 (modelWithCornersSelf ℂ E) (g ∘ f) x) = _
  rw [mfderiv_comp x hg hf]
  exact ContinuousLinearMap.comp_assoc _ _ _

end JacobianChallenge.TraceDegree
