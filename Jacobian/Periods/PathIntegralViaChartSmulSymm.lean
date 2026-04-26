import Jacobian.Periods.PathIntegralViaChartLinear
import Jacobian.Periods.PathLiftSimp

/-!
# Provisional via-chart `_smul`/`_symm` corollary

Provisional from-`X` analogue of `pathIntegralViaChartCorrect_smul_symm`:
in a single chart `c` whose source contains both `γ` and `γ.symm`,
integrating `k • ω` along `γ.symm` equals `-(k • pathIntegralViaChart c ω γ h)`.
Uses the simpler `chartedForm` (which drops the `mfderiv` factor).

One-line `rw` corollary combining the just-landed via-chart provisional
`_smul`, `_symm`, and `smul_neg`.
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Scalar-multiplication along the reversed path (provisional via-chart):
`k • ω` along `γ.symm` equals minus `k • pathIntegralViaChart c ω γ h`. -/
theorem pathIntegralViaChart_smul_symm
    (c : OpenPartialHomeomorph X E) (k : ℂ) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b)
    (h : range γ ⊆ c.source) (h' : range γ.symm ⊆ c.source) :
    pathIntegralViaChart c (k • ω) γ.symm h' =
      -(k • pathIntegralViaChart c ω γ h) := by
  rw [pathIntegralViaChart_smul, pathIntegralViaChart_symm c ω γ h h', smul_neg]

end JacobianChallenge.Periods
