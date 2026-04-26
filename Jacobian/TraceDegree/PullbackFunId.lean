import Jacobian.TraceDegree.PullbackFun
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Pullback along the identity map is the identity. -/
@[simp] theorem pullbackFormsFun_id
    (η : HolomorphicOneForm E X) :
    pullbackFormsFun (id : X → X) η = η.toFun := by
  funext x
  show (η.toFun (id x)).comp
         (mfderiv (modelWithCornersSelf ℂ E)
                  (modelWithCornersSelf ℂ E) id x) = η.toFun x
  rw [mfderiv_id]
  exact ContinuousLinearMap.comp_id _

end JacobianChallenge.TraceDegree
