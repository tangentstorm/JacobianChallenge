import Jacobian.Periods.PathIntegralViaCover
import Jacobian.Periods.DivFinIcc
import Mathlib.Topology.Subpath

namespace JacobianChallenge.Periods

open Set JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
`pathIntegralViaCoverWith` unfolds to the explicit `Finset.sum`
over `Fin n` of chart-local integrals on each subpath.
-/
theorem pathIntegralViaCoverWith_apply
    (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b)
    (n : ℕ) (hn : 0 < n) (pickChart : Fin n → X)
    (hcov : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt E (pickChart i)).source) :
    pathIntegralViaCoverWith ω γ n hn pickChart hcov =
      ∑ i : Fin n,
        pathIntegralViaChartCorrect (chartAt E (pickChart i)) ω
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
            exact hcov i t hle1 hle2) := rfl

end JacobianChallenge.Periods
