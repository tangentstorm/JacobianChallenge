import Jacobian.Periods.PathPartition
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Converting a cover for `γ` into one for `γ.symm`

If `pickChart : Fin n → X` and `hcov` cover `γ` segment-by-segment,
then `pickChart ∘ Fin.rev` and a derived `hcov_symm` cover `γ.symm`
segment-by-segment.

The intuition: segment `i` of `γ.symm` runs from time `i/n` to
`(i+1)/n`, which under `γ.symm t = γ (σ t) = γ (1 - t)` corresponds
to `γ` running from time `1 - (i+1)/n = (n - i - 1)/n` to
`1 - i/n = (n - i)/n`. That's segment `n - 1 - i` of `γ`, i.e.
`Fin.rev i`. So `pickChart (Fin.rev i)` covers segment `i` of `γ.symm`.

This is a structural ingredient for `pathIntegralViaCoverWith_symm`.
-/

namespace JacobianChallenge.Periods

open unitInterval

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]

/--
A cover of `γ` by `pickChart` reindexed via `Fin.rev` covers
`γ.symm`.
-/
theorem cover_symm_of_cover
    {a b : X} (γ : Path a b)
    (n : ℕ) (hn : 0 < n) (pickChart : Fin n → X)
    (hcov : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt E (pickChart i)).source) :
    ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ.symm t ∈ (chartAt E (pickChart (Fin.rev i))).source := by
  intro i t hlo hhi
  -- γ.symm t = γ (σ t); apply hcov at index Fin.rev i and time σ t
  show γ (σ t) ∈ (chartAt E (pickChart (Fin.rev i))).source
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hi : i.val + 1 ≤ n := i.isLt
  -- Strip divisions from hlo/hhi to use linarith cleanly
  have hlo' : (i.val : ℝ) ≤ (t : ℝ) * n := by
    rw [div_le_iff₀ hn'] at hlo; exact hlo
  have hhi' : (t : ℝ) * n ≤ (i.val : ℝ) + 1 := by
    rw [le_div_iff₀ hn'] at hhi; exact hhi
  refine hcov (Fin.rev i) (σ t) ?_ ?_
  · -- ((Fin.rev i : ℕ) : ℝ) / n ≤ (σ t : ℝ) = 1 - (t : ℝ)
    rw [Fin.val_rev, coe_symm_eq, Nat.cast_sub hi, div_le_iff₀ hn']
    push_cast
    linarith
  · -- (σ t : ℝ) = 1 - (t : ℝ) ≤ ((Fin.rev i : ℕ) : ℝ + 1) / n
    rw [Fin.val_rev, coe_symm_eq, Nat.cast_sub hi, le_div_iff₀ hn']
    push_cast
    linarith

end JacobianChallenge.Periods
