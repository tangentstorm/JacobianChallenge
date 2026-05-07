import Jacobian.Periods.LebesgueChartRadius
import Mathlib.Topology.Path
import Mathlib.Topology.UnitInterval
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs

namespace JacobianChallenge.Periods

open Set Metric unitInterval

/-- For a continuous path `γ` from a compact metric space `K = unitInterval`
into a charted space `X`, there exists `n ≥ 1` and a chart-selection
function `pickChart : Fin n → X` such that for every sub-interval
`[i/n, (i+1)/n]` and every `t` in that sub-interval, `γ t` lies in
`(chartAt E (pickChart i)).source`.
-/
lemma exists_uniform_chart_partition
    (E : Type*) [TopologicalSpace E]
    {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
    (γ : C(unitInterval, X)) :
    ∃ (n : ℕ) (_ : 0 < n) (pickChart : Fin n → X),
      ∀ (i : Fin n) (t : unitInterval),
        (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
        γ t ∈ (chartAt E (pickChart i)).source := by
  have := @exists_lebesgue_radius_chart;
  obtain ⟨ δ, δ_pos, hδ ⟩ := @this I _ _ E _ X _ _ γ;
  -- Choose `n` such that `1/n < δ`.
  obtain ⟨n, hn⟩ : ∃ n : ℕ+, (1 / (n : ℝ)) < δ := by
    exact ⟨ ⟨ ⌊δ⁻¹⌋₊ + 1, Nat.succ_pos _ ⟩, by simpa using inv_lt_of_inv_lt₀ δ_pos <| Nat.lt_floor_add_one _ ⟩;
  choose f hf using hδ;
  refine' ⟨ n, n.pos, fun i => f ⟨ ( i : ℝ ) / n + 1 / ( 2 * n ), _, _ ⟩, fun i t ht₁ ht₂ => hf _ _ ⟩ <;> norm_num at *;
  any_goals positivity;
  any_goals rw [ Subtype.dist_eq ] ; norm_num;
  · nlinarith [ show ( i : ℝ ) + 1 ≤ n from mod_cast Nat.succ_le_of_lt i.2, mul_inv_cancel₀ ( by positivity : ( n : ℝ ) ≠ 0 ), div_mul_cancel₀ ( ( i : ℝ ) : ℝ ) ( by positivity : ( n : ℝ ) ≠ 0 ) ];
  · refine' abs_lt.mpr ⟨ _, _ ⟩ <;> ring_nf at * <;> linarith

end JacobianChallenge.Periods