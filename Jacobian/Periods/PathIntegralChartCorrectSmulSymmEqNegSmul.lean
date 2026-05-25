import Jacobian.Periods.PathIntegralChartCorrectSimp
import Jacobian.Periods.PathIntegralChartCorrectSmul

/-!
# Scalar negation absorbs path reversal (in-chart, corrected)

In-chart corrected analogue of
`pathIntegralViaChartCorrect_smul_symm_eq_neg_smul`:
`∫(k • ω, γ.symm) = ∫((-k) • ω, γ)`. Composes `_smul`, `_symm`,
`neg_smul`. Foundational case for the cover-layer version.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
Scalar negation absorbs path reversal (in-chart, corrected):
`∫(k • ω, γ.symm) = ∫((-k) • ω, γ)`.
-/
theorem pathIntegralInChartCorrect_smul_symm_eq_neg_smul
    (c : OpenPartialHomeomorph X E) (k : ℂ) (ω : HolomorphicOneForm E X)
    {a b : E} (γ : Path a b) :
    pathIntegralInChartCorrect c (k • ω) γ.symm =
      pathIntegralInChartCorrect c ((-k) • ω) γ := by
  rw [pathIntegralInChartCorrect_smul, pathIntegralInChartCorrect_symm,
      pathIntegralInChartCorrect_smul, neg_smul, smul_neg]

end JacobianChallenge.Periods
