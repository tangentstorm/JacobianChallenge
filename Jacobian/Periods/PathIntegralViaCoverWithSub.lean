import Jacobian.Periods.PathIntegralViaCover
import Jacobian.Periods.PathIntegralViaChartCorrectSub

/-!
# Conditional subtraction linearity of `pathIntegralViaCoverWith`

Lifts the per-chart conditional `_sub` from
`pathIntegralViaChartCorrect_sub_of_curveIntegrable` across the
`Finset.sum` over the partition, parallel to the `_add` ladder.
Per-segment `CurveIntegrable` hypotheses are required for each form;
the multi-chart sum then distributes via `Finset.sum_sub_distrib`.

Becomes unconditional once Packet F lands.
-/

namespace JacobianChallenge.Periods

open Set unitInterval JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Conditional subtraction linearity of `pathIntegralViaCoverWith`:
if for every segment `i` both chart pullbacks are curve-integrable
along the chart-lifted subpath, the multi-chart integral
distributes over subtraction. -/
theorem pathIntegralViaCoverWith_sub_of_curveIntegrable
    (ω η : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b)
    (n : ℕ) (hn : 0 < n) (pickChart : Fin n → X)
    (hcov : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt E (pickChart i)).source)
    (hω : ∀ i : Fin n,
      CurveIntegrable (chartedFormPullback (chartAt E (pickChart i)) ω)
        (chartLift (chartAt E (pickChart i))
          (γ.subpath (divFinIcc n hn i.val (le_of_lt i.isLt))
                     (divFinIcc n hn (i.val + 1) i.isLt))
          (by
            rw [Path.range_subpath]
            intro x hx
            obtain ⟨t, ht, rfl⟩ := hx
            rw [Set.uIcc_of_le (divFinIcc_le_succ n hn i.val i.isLt)] at ht
            rcases Set.mem_Icc.mp ht with ⟨h1, h2⟩
            have hle1 : ((i.val : ℝ) / n) ≤ (t : ℝ) := h1
            have hle2 : (t : ℝ) ≤ ((i.val : ℝ) + 1) / n := by
              have h2' : (t : ℝ) ≤ (divFinIcc n hn (i.val + 1) i.isLt : ℝ) := h2
              rw [divFinIcc_val] at h2'
              push_cast at h2'
              exact h2'
            exact hcov i t hle1 hle2)))
    (hη : ∀ i : Fin n,
      CurveIntegrable (chartedFormPullback (chartAt E (pickChart i)) η)
        (chartLift (chartAt E (pickChart i))
          (γ.subpath (divFinIcc n hn i.val (le_of_lt i.isLt))
                     (divFinIcc n hn (i.val + 1) i.isLt))
          (by
            rw [Path.range_subpath]
            intro x hx
            obtain ⟨t, ht, rfl⟩ := hx
            rw [Set.uIcc_of_le (divFinIcc_le_succ n hn i.val i.isLt)] at ht
            rcases Set.mem_Icc.mp ht with ⟨h1, h2⟩
            have hle1 : ((i.val : ℝ) / n) ≤ (t : ℝ) := h1
            have hle2 : (t : ℝ) ≤ ((i.val : ℝ) + 1) / n := by
              have h2' : (t : ℝ) ≤ (divFinIcc n hn (i.val + 1) i.isLt : ℝ) := h2
              rw [divFinIcc_val] at h2'
              push_cast at h2'
              exact h2'
            exact hcov i t hle1 hle2))) :
    pathIntegralViaCoverWith (ω - η) γ n hn pickChart hcov =
      pathIntegralViaCoverWith ω γ n hn pickChart hcov -
        pathIntegralViaCoverWith η γ n hn pickChart hcov := by
  unfold pathIntegralViaCoverWith
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact pathIntegralViaChartCorrect_sub_of_curveIntegrable
    (chartAt E (pickChart i)) ω η _ _ (hω i) (hη i)

end JacobianChallenge.Periods
