import Jacobian.TraceDegree.PullbackFun

/-!
# Scalar-multiplication linearity of `pullbackFormsFun`

Shows that `pullbackFormsFun f (k • η) = k • pullbackFormsFun f η`,
completing the ℂ-linearity API alongside `pullbackFormsFun_zero`,
`pullbackFormsFun_neg`, and `pullbackFormsFun_add`.
-/

namespace JacobianChallenge.TraceDegree

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace E Y]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) Y]

/-- The pullback function is ℂ-linear in the form. -/
@[simp] theorem pullbackFormsFun_smul
    (f : X → Y) (k : ℂ) (η : HolomorphicOneForm E Y) :
    pullbackFormsFun f (k • η) = k • pullbackFormsFun f η := by
  funext x
  show ((k • η).toFun (f x)).comp
         (mfderiv (modelWithCornersSelf ℂ E)
                  (modelWithCornersSelf ℂ E) f x) =
       k • ((η.toFun (f x)).comp
         (mfderiv (modelWithCornersSelf ℂ E)
                  (modelWithCornersSelf ℂ E) f x))
  have hcoe : ((k • η) : ∀ x, _) (f x) = k • (η : ∀ x, _) (f x) := by
    rw [ContMDiffSection.coe_smul]
    rfl
  rw [show (k • η).toFun (f x) = k • (η.toFun (f x)) from hcoe]
  exact ContinuousLinearMap.smul_comp _ _ _

end JacobianChallenge.TraceDegree
