import Jacobian.Periods.PathIntegralViaCoverNeg
import Jacobian.Periods.PathIntegralViaCoverSmul

/-!
# Cover-layer: form-negation factors through scalar negation

Cover-layer analogue: `∫(-(k • ω), γ) = (-k) • ∫(ω, γ)`.
Composes `_neg + _smul + ← neg_smul`.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
Cover-layer: form-negation of a scalar multiple equals the
negated scalar multiple of the integral.
-/
theorem pathIntegralViaCoverWith_neg_smul
    (k : ℂ) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b)
    (n : ℕ) (hn : 0 < n) (pickChart : Fin n → X)
    (hcov : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt E (pickChart i)).source) :
    pathIntegralViaCoverWith (-(k • ω)) γ n hn pickChart hcov =
      (-k) • pathIntegralViaCoverWith ω γ n hn pickChart hcov := by
  rw [pathIntegralViaCoverWith_neg, pathIntegralViaCoverWith_smul, ← neg_smul]

end JacobianChallenge.Periods
