import Mathlib.Topology.UnitInterval

/-!
# Boundary points `i/n` of the unit interval

A small helper file providing `divFinIcc n hn i hi : unitInterval`,
the boundary point `i/n` of the unit interval for `0 < n` and
`i ≤ n`. Used by the planned `pathIntegralViaCover` (multi-chart
path integral): the i-th segment runs from `divFinIcc n hn i _` to
`divFinIcc n hn (i+1) _`.
-/

namespace JacobianChallenge.Periods

open unitInterval

/-- Boundary point `i / n : unitInterval` for `i ≤ n`, given `0 < n`. -/
noncomputable def divFinIcc (n : ℕ) (hn : 0 < n) (i : ℕ) (hi : i ≤ n) :
    unitInterval :=
  ⟨(i : ℝ) / n, by
    refine ⟨?_, ?_⟩
    · positivity
    · rw [div_le_one (by exact_mod_cast hn)]
      exact_mod_cast hi⟩

@[simp] theorem divFinIcc_val
    (n : ℕ) (hn : 0 < n) (i : ℕ) (hi : i ≤ n) :
    (divFinIcc n hn i hi : ℝ) = (i : ℝ) / n := rfl

@[simp] theorem divFinIcc_zero (n : ℕ) (hn : 0 < n) :
    divFinIcc n hn 0 (Nat.zero_le n) = (0 : unitInterval) := by
  apply Subtype.ext
  simp [divFinIcc]

@[simp] theorem divFinIcc_self (n : ℕ) (hn : 0 < n) :
    divFinIcc n hn n (le_refl n) = (1 : unitInterval) := by
  apply Subtype.ext
  show ((n : ℝ) / n : ℝ) = 1
  field_simp

theorem divFinIcc_le_succ
    (n : ℕ) (hn : 0 < n) (i : ℕ) (hi : i + 1 ≤ n) :
    divFinIcc n hn i (Nat.le_of_succ_le hi) ≤ divFinIcc n hn (i+1) hi := by
  rw [Subtype.mk_le_mk]
  show (i : ℝ) / n ≤ ((i + 1 : ℕ) : ℝ) / n
  rw [div_le_div_iff_of_pos_right (by exact_mod_cast hn)]
  push_cast
  linarith

/-- Reflection of a partition boundary: `σ (i/n) = (n - i)/n`. Useful
when reflecting a path partition under `Path.symm` (partition point
`t` of `γ` corresponds to `1 - t` of `γ.symm`). -/
theorem divFinIcc_symm
    (n : ℕ) (hn : 0 < n) (i : ℕ) (hi : i ≤ n) :
    σ (divFinIcc n hn i hi) = divFinIcc n hn (n - i) (Nat.sub_le n i) := by
  apply Subtype.ext
  show 1 - (i : ℝ) / n = ((n - i : ℕ) : ℝ) / n
  rw [Nat.cast_sub hi, sub_div,
      div_self (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0)]

end JacobianChallenge.Periods
