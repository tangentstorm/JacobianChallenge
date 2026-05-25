import Jacobian.Periods.PathIntegralViaChartLinear
import Jacobian.Periods.PathLiftSimp

/-!
# Scalar negation absorbs path reversal (provisional via-chart)

Provisional via-chart analogue of
`pathIntegralViaChartCorrect_smul_symm_eq_neg_smul`:
`∫(k • ω, γ.symm) = ∫((-k) • ω, γ)`. Uses the simpler `chartedForm`
(which drops the `mfderiv` factor). Completes the family across
all five layers.
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
Scalar negation absorbs path reversal (provisional via-chart):
`∫(k • ω, γ.symm) = ∫((-k) • ω, γ)`.
-/
theorem pathIntegralViaChart_smul_symm_eq_neg_smul
    (c : OpenPartialHomeomorph X E) (k : ℂ) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b)
    (h : range γ ⊆ c.source) (h' : range γ.symm ⊆ c.source) :
    pathIntegralViaChart c (k • ω) γ.symm h' =
      pathIntegralViaChart c ((-k) • ω) γ h := by
  rw [pathIntegralViaChart_smul, pathIntegralViaChart_symm c ω γ h h',
      pathIntegralViaChart_smul, neg_smul, smul_neg]

end JacobianChallenge.Periods
