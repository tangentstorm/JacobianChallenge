import Jacobian.Periods.PathIntegralViaChartCorrectSmul
import Jacobian.Periods.PathIntegralViaChartCorrect

/-!
# Scalar-multiplication along reversed path (single-chart, corrected)

Single-chart analogue of `pathIntegralViaCoverWith_smul_symm`: in a
single chart `c` whose source contains both `γ` and `γ.symm`,
integrating `k • ω` along `γ.symm` equals `-(k • pathIntegralViaChartCorrect c ω γ)`.

One-line `rw` corollary combining `_smul`, `_symm`, and `smul_neg`.
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Scalar-multiplication along the reversed path (single-chart):
`k • ω` along `γ.symm` equals minus `k • (via-chart integral of ω along γ)`. -/
theorem pathIntegralViaChartCorrect_smul_symm
    (c : OpenPartialHomeomorph X E) (k : ℂ) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b)
    (h : range γ ⊆ c.source) (h' : range γ.symm ⊆ c.source) :
    pathIntegralViaChartCorrect c (k • ω) γ.symm h' =
      -(k • pathIntegralViaChartCorrect c ω γ h) := by
  rw [pathIntegralViaChartCorrect_smul, pathIntegralViaChartCorrect_symm c ω γ h h',
      smul_neg]

end JacobianChallenge.Periods
