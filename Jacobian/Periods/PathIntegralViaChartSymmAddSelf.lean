import Jacobian.Periods.PathLiftSimp

/-!
Provisional from-`X` analogue of `pathIntegralViaChartCorrect_add_symm_self`:
in a single chart `c` whose source contains both `γ` and `γ.symm`,
`pathIntegralViaChart c ω γ + pathIntegralViaChart c ω γ.symm = 0`. Uses
the simpler `chartedForm` (which drops the `mfderiv` factor).
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]


theorem pathIntegralViaChart_add_symm_self
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b)
    (h : range γ ⊆ c.source) (h' : range γ.symm ⊆ c.source) :
    pathIntegralViaChart c ω γ h +
        pathIntegralViaChart c ω γ.symm h' = 0 := by
  rw [pathIntegralViaChart_symm c ω γ h h', add_neg_cancel]

end JacobianChallenge.Periods
