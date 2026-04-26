import Jacobian.Periods.PathIntegralChartCorrectSmul
import Jacobian.Periods.PathIntegralChartCorrectSimp

/-!
# In-chart corrected `_smul`/`_symm` corollary

In-chart corrected analogue of `pathIntegralViaChartCorrect_smul_symm`:
for a chart-coordinate path `γ : Path a b` (with `a b : E`),
integrating `k • ω` along `γ.symm` equals `-(k • pathIntegralInChartCorrect c ω γ)`.

One-line `rw` corollary combining the just-landed in-chart `_smul`,
`_symm`, and `smul_neg`. Foundational for cover-level `_smul_symm`
chains (already in place at the via-chart and cover layers).
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Scalar-multiplication along the reversed path (in-chart corrected):
`k • ω` along `γ.symm` equals minus `k • pathIntegralInChartCorrect c ω γ`. -/
theorem pathIntegralInChartCorrect_smul_symm
    (c : OpenPartialHomeomorph X E) (k : ℂ) (ω : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b) :
    pathIntegralInChartCorrect c (k • ω) γ.symm =
      -(k • pathIntegralInChartCorrect c ω γ) := by
  rw [pathIntegralInChartCorrect_smul, pathIntegralInChartCorrect_symm, smul_neg]

end JacobianChallenge.Periods
