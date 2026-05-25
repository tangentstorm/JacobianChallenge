import Jacobian.Periods.PathIntegralChartLinear
import Jacobian.Periods.PathIntegralChart

/-!
# Provisional in-chart `_smul`/`_symm` corollary

Provisional in-chart analogue of `pathIntegralInChartCorrect_smul_symm`:
for a chart-coordinate path `γ : Path a b` (with `a b : E`),
integrating `k • ω` along `γ.symm` equals `-(k • pathIntegralInChart c ω γ)`.

One-line `rw` corollary combining the provisional `_smul`,
`_symm`, and `smul_neg`. Uses the simpler `chartedForm` (no `mfderiv`
factor).
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
Scalar-multiplication along the reversed path (provisional in-chart):
`k • ω` along `γ.symm` equals minus `k • pathIntegralInChart c ω γ`.
-/
theorem pathIntegralInChart_smul_symm
    (c : OpenPartialHomeomorph X E) (k : ℂ) (ω : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b) :
    pathIntegralInChart c (k • ω) γ.symm =
      -(k • pathIntegralInChart c ω γ) := by
  rw [pathIntegralInChart_smul, pathIntegralInChart_symm, smul_neg]

end JacobianChallenge.Periods
