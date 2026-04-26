import Jacobian.TraceDegree.PullbackFormsLinearMapApply
import Jacobian.TraceDegree.PullbackFunComp
import Jacobian.TraceDegree.PullbackFunCompApply

/-!
# Bundled-LinearMap-level chain rule (pointwise)

Pointwise lifts of `pullbackFormsFun_comp_apply` and
`pullbackFormsFun_comp_apply_apply` to the bundled
`pullbackFormsLinearMap`. Since `pullbackFormsFun g η` is just a
function (smoothness deferred), there is no global LinearMap
composition; these pointwise forms are the natural bundled
analogues.
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
/-- Bundled-level chain rule (pointwise): `pullbackFormsLinearMap`
on a composition factors through `mfderiv` of both maps. -/
theorem pullbackFormsLinearMap_comp_apply_at
    (f : X → Y) (g : Y → Z) (η : HolomorphicOneForm E Z) (x : X)
    (hg : MDifferentiableAt (modelWithCornersSelf ℂ E)
                            (modelWithCornersSelf ℂ E) g (f x))
    (hf : MDifferentiableAt (modelWithCornersSelf ℂ E)
                            (modelWithCornersSelf ℂ E) f x) :
    pullbackFormsLinearMap (g ∘ f) η x =
      ((η.toFun (g (f x))).comp
        (mfderiv (modelWithCornersSelf ℂ E)
                 (modelWithCornersSelf ℂ E) g (f x))).comp
        (mfderiv (modelWithCornersSelf ℂ E)
                 (modelWithCornersSelf ℂ E) f x) := by
  rw [pullbackFormsLinearMap_apply_at, pullbackFormsFun_comp_apply f g η x hg hf]

set_option linter.unusedSectionVars false in
/-- Bundled-level chain rule, evaluated on a tangent vector. -/
theorem pullbackFormsLinearMap_comp_apply_vec
    (f : X → Y) (g : Y → Z) (η : HolomorphicOneForm E Z)
    (x : X) (v : E)
    (hg : MDifferentiableAt (modelWithCornersSelf ℂ E)
                            (modelWithCornersSelf ℂ E) g (f x))
    (hf : MDifferentiableAt (modelWithCornersSelf ℂ E)
                            (modelWithCornersSelf ℂ E) f x) :
    pullbackFormsLinearMap (g ∘ f) η x v =
      η.toFun (g (f x))
        (mfderiv (modelWithCornersSelf ℂ E)
                 (modelWithCornersSelf ℂ E) g (f x)
          (mfderiv (modelWithCornersSelf ℂ E)
                   (modelWithCornersSelf ℂ E) f x v)) := by
  rw [pullbackFormsLinearMap_apply_at]
  exact pullbackFormsFun_comp_apply_apply f g η x v hg hf

end JacobianChallenge.TraceDegree
