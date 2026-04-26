import Jacobian.Periods.PathIntegralViaCover
import Jacobian.Periods.PathIntegralViaChartCorrectZero

/-!
# `pathIntegralViaCoverWith` is zero on the zero form

The integral of the zero 1-form is zero on every segment, so the
multi-chart sum is zero. Negation/addition variants are deferred:
`_neg` waits on `40031834` (`pathIntegralViaChartCorrect_neg`),
and `_add` waits on the integrability helper (Packet F).
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- The multi-chart path integral of the zero form is zero. -/
@[simp] theorem pathIntegralViaCoverWith_zero
    {a b : X} (γ : Path a b)
    (n : ℕ) (hn : 0 < n) (pickChart : Fin n → X)
    (hcov : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt E (pickChart i)).source) :
    pathIntegralViaCoverWith (0 : HolomorphicOneForm E X)
      γ n hn pickChart hcov = 0 := by
  unfold pathIntegralViaCoverWith
  apply Finset.sum_eq_zero
  intro i _
  exact pathIntegralViaChartCorrect_zero _ _ _

end JacobianChallenge.Periods
