import Jacobian.Periods.PathPartition
import Jacobian.Periods.DivFinIcc
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Subpath

/-!
# Cover for the σ-form γ-segment at index `Fin.rev i`

The σ-form path `γ.subpath (σ (divFinIcc (i+1))) (σ (divFinIcc i))`
parameterises γ over `[σ((i+1)/n), σ(i/n)] = [(n-i-1)/n, (n-i)/n]`,
which is exactly segment `Fin.rev i = n-1-i` of γ. Therefore an
`hcov` covering γ segment-by-segment also covers this σ-form path
when we apply it at index `Fin.rev i`.

Used to construct the range hypothesis required by
`pathIntegralViaChartCorrect_symm_subpath_divFinIcc` inside the
`pathIntegralViaCoverWith_symm` proof.
-/

namespace JacobianChallenge.Periods

open Set unitInterval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]

set_option linter.unusedSectionVars false

/--
The σ-form γ-segment at index `Fin.rev i` is covered by
`pickChart (Fin.rev i)`.
-/
theorem range_subpath_sigma_subset_source
    {a b : X} (γ : Path a b)
    (n : ℕ) (hn : 0 < n) (pickChart : Fin n → X)
    (hcov : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt E (pickChart i)).source)
    (i : Fin n) :
    range (γ.subpath
        (σ (divFinIcc n hn (i.val + 1) i.isLt))
        (σ (divFinIcc n hn i.val (Nat.le_of_succ_le i.isLt)))) ⊆
      (chartAt E (pickChart (Fin.rev i))).source := by
  rw [Path.range_subpath]
  intro x hx
  obtain ⟨t, ht, rfl⟩ := hx
  -- t ∈ uIcc (σ (divFinIcc (i+1))) (σ (divFinIcc i))
  -- σ ((i+1)/n) = (n-i-1)/n ≤ σ (i/n) = (n-i)/n, so uIcc = Icc
  have hle : σ (divFinIcc n hn (i.val + 1) i.isLt) ≤
             σ (divFinIcc n hn i.val (Nat.le_of_succ_le i.isLt)) := by
    rw [symm_le_symm]
    exact divFinIcc_le_succ n hn i.val i.isLt
  rw [Set.uIcc_of_le hle] at ht
  rcases Set.mem_Icc.mp ht with ⟨h1, h2⟩
  -- (σ ((i+1)/n) : ℝ) = 1 - (i+1)/n = (n-i-1)/n ≤ (t : ℝ)
  -- (t : ℝ) ≤ (σ (i/n) : ℝ) = 1 - i/n = (n-i)/n
  have hlo : ((Fin.rev i).val : ℝ) / n ≤ (t : ℝ) := by
    have h1_R : (σ (divFinIcc n hn (i.val + 1) i.isLt) : ℝ) ≤ (t : ℝ) := h1
    rw [coe_symm_eq, divFinIcc_val] at h1_R
    push_cast at h1_R
    -- h1_R : 1 - ((i.val : ℝ) + 1) / n ≤ (t : ℝ)  (or similar)
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hi : i.val + 1 ≤ n := i.isLt
    rw [Fin.val_rev, Nat.cast_sub hi, div_le_iff₀ hn']
    push_cast
    have hmul := mul_le_mul_of_nonneg_right h1_R hn'.le
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hn'.ne'] at hmul
    linarith
  have hhi : (t : ℝ) ≤ (((Fin.rev i).val : ℝ) + 1) / n := by
    have h2_R : (t : ℝ) ≤ (σ (divFinIcc n hn i.val (Nat.le_of_succ_le i.isLt)) : ℝ) := h2
    rw [coe_symm_eq, divFinIcc_val] at h2_R
    -- h2_R : (t : ℝ) ≤ 1 - (i.val : ℝ) / n
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hi : i.val + 1 ≤ n := i.isLt
    rw [Fin.val_rev, Nat.cast_sub hi, le_div_iff₀ hn']
    push_cast
    have hmul := mul_le_mul_of_nonneg_right h2_R hn'.le
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hn'.ne'] at hmul
    linarith
  exact hcov (Fin.rev i) t hlo hhi

end JacobianChallenge.Periods
