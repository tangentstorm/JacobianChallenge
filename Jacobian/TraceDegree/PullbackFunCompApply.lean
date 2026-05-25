import Jacobian.TraceDegree.PullbackFunComp

/-!
# Tangent-vector application form of the chain-rule pullback

Apply form of `pullbackFormsFun_comp_apply`, evaluating on a tangent
vector `v`. Gives the fully-unrolled chain-rule formula
`(g ∘ f)^*η _x v = η_{g(f x)} (mfderiv g (f x) (mfderiv f x v))`.

Conditional on `MDifferentiableAt` for both maps (inherited from
`pullbackFormsFun_comp_apply`).
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
Tangent-vector apply form of `pullbackFormsFun_comp_apply`:
the chain-rule pullback evaluated on `v` is `η` at `g(f x)` applied
to `mfderiv g (f x) (mfderiv f x v)`.
-/
theorem pullbackFormsFun_comp_apply_apply
    (f : X → Y) (g : Y → Z) (η : HolomorphicOneForm E Z)
    (x : X) (v : E)
    (hg : MDifferentiableAt (modelWithCornersSelf ℂ E)
                            (modelWithCornersSelf ℂ E) g (f x))
    (hf : MDifferentiableAt (modelWithCornersSelf ℂ E)
                            (modelWithCornersSelf ℂ E) f x) :
    pullbackFormsFun (g ∘ f) η x v =
      η.toFun (g (f x))
        (mfderiv (modelWithCornersSelf ℂ E)
                 (modelWithCornersSelf ℂ E) g (f x)
          (mfderiv (modelWithCornersSelf ℂ E)
                   (modelWithCornersSelf ℂ E) f x v)) := by
  rw [pullbackFormsFun_comp_apply f g η x hg hf]
  rfl

end JacobianChallenge.TraceDegree
