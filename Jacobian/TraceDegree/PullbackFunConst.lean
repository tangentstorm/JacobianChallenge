import Jacobian.TraceDegree.PullbackFun
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Pullback of a holomorphic 1-form along a constant map

The pullback along a constant map `Function.const X y` is the zero
function, because the `mfderiv` of a constant map is the zero
continuous linear map.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

/-- The pullback along a constant map is zero. -/
@[simp] theorem pullbackFormsFun_const
    (y : Y) (η : HolomorphicOneForm E Y) :
    pullbackFormsFun (Function.const X y) η = 0 := by
  funext x
  show ((η.toFun (Function.const X y x)).comp
         (mfderiv (modelWithCornersSelf ℂ E)
                  (modelWithCornersSelf ℂ E)
                  (Function.const X y) x) : E →L[ℂ] ℂ) = 0
  rw [show Function.const X y = (fun _ : X => y) from rfl, mfderiv_const]
  exact ContinuousLinearMap.comp_zero _

end JacobianChallenge.TraceDegree
