import Jacobian.Periods.PathIntegralViaChartCorrectSmul
import Jacobian.Periods.PathIntegralViaChartCorrect

/-!
# Scalar negation absorbs path reversal (single-chart, corrected)

`∫(k • ω, γ.symm) = ∫((-k) • ω, γ)`: path reversal can be absorbed
into a sign flip on the scalar. Composes `_smul_symm` with `_smul`
and `neg_smul` to turn the right-hand side into the standard form.

Useful when one side of an identity has a reversed path and the
other doesn't, but the form scales differently.
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
Scalar negation absorbs path reversal: `∫(k • ω, γ.symm) =
∫((-k) • ω, γ)`.
-/
theorem pathIntegralViaChartCorrect_smul_symm_eq_neg_smul
    (c : OpenPartialHomeomorph X E) (k : ℂ) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b)
    (h : range γ ⊆ c.source) (h' : range γ.symm ⊆ c.source) :
    pathIntegralViaChartCorrect c (k • ω) γ.symm h' =
      pathIntegralViaChartCorrect c ((-k) • ω) γ h := by
  rw [pathIntegralViaChartCorrect_smul, pathIntegralViaChartCorrect_symm c ω γ h h',
      pathIntegralViaChartCorrect_smul, neg_smul, smul_neg]

end JacobianChallenge.Periods
