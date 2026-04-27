import Jacobian.Periods.PathIntegralViaCover

/-!
# Range subset for cover-with chart segments

A reusable named version of the range-subset proof that appears
inline in `pathIntegralViaCoverWith` (and would otherwise have to be
repeated everywhere we want to talk about the i-th chart segment of
a uniform-cover partition). Given a partition witnessed by `hcov`
and a segment `i : Fin n`, the i-th subpath
`γ.subpath (divFinIcc … i …) (divFinIcc … (i+1) …)` lies in
`(chartAt E (pickChart i)).source`.
-/

namespace JacobianChallenge.Periods

open Set unitInterval JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

set_option linter.unusedSectionVars false in
/-- The i-th cover segment of `γ` lies in the i-th chart's source. -/
theorem cover_segment_subpath_range
    {a b : X} (γ : Path a b)
    (n : ℕ) (hn : 0 < n) (pickChart : Fin n → X)
    (hcov : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt E (pickChart i)).source)
    (i : Fin n) :
    range (γ.subpath (divFinIcc n hn i.val (le_of_lt i.isLt))
                     (divFinIcc n hn (i.val + 1) i.isLt)) ⊆
      (chartAt E (pickChart i)).source := by
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
  exact hcov i t hle1 hle2

end JacobianChallenge.Periods
