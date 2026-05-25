import Jacobian.Periods.PathIntegralViaCover
import Jacobian.Periods.PathIntegralViaChartCorrectEqOfMfderivId
import Jacobian.Periods.CoverSegmentSubpathRange
import Jacobian.Periods.PathLift

/-!
# Cover-with bridge under `mfderiv c.symm = id` everywhere

Lifts the per-chart bridge to the multi-chart cover-with sum. Under
the per-segment hypothesis `∀ i e, mfderiv (chartAt E (pickChart i)).symm e = id`,
each summand of `pathIntegralViaCoverWith` (which uses the corrected
chart-pullback) coincides with the provisional via-chart integral
on that segment.
-/

namespace JacobianChallenge.Periods

open Set unitInterval JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
If on every segment chart `mfderiv c.symm` is identity everywhere,
the cover-with integral equals the segment-wise sum of provisional
via-chart integrals.
-/
theorem pathIntegralViaCoverWith_eq_sum_provisional_of_mfderiv_id
    (ω : HolomorphicOneForm E X) {a b : X} (γ : Path a b)
    (n : ℕ) (hn : 0 < n) (pickChart : Fin n → X)
    (hcov : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt E (pickChart i)).source)
    (hd : ∀ (i : Fin n) (e : E),
      mfderiv (modelWithCornersSelf ℂ E)
              (modelWithCornersSelf ℂ E)
              (chartAt E (pickChart i)).symm e =
        ContinuousLinearMap.id ℂ E) :
    pathIntegralViaCoverWith ω γ n hn pickChart hcov =
      ∑ i : Fin n,
        pathIntegralViaChart (chartAt E (pickChart i)) ω
          (γ.subpath (divFinIcc n hn i.val (le_of_lt i.isLt))
                     (divFinIcc n hn (i.val + 1) i.isLt))
          (cover_segment_subpath_range γ n hn pickChart hcov i) := by
  unfold pathIntegralViaCoverWith
  apply Finset.sum_congr rfl
  intro i _
  exact pathIntegralViaChartCorrect_eq_pathIntegralViaChart_of_mfderiv_id
    (chartAt E (pickChart i)) ω _ _ (hd i)

end JacobianChallenge.Periods
