import Jacobian.Periods.LebesgueChartRadius
import Mathlib.Topology.Path
import Mathlib.Topology.UnitInterval
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
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

/-- **Refined Lebesgue partition with chart-coord ball coverage.** Strengthening
of `exists_uniform_chart_partition` for the `ℂ`-charted-space case: in addition
to chart-source coverage, supplies for each segment `i` a radius `r_i > 0` and
guarantees that every `γ t` for `t ∈ [i/n, (i+1)/n]` has its chart-image inside
`Metric.ball (chartAt ℂ (pickChart i)(pickChart i)) r_i`, with the ball
contained in `(chartAt ℂ (pickChart i)).target`.

This is the input to the V→Λ trick in `exists_chartContDiffPath_in_chart`: the
ball-coord coverage is exactly what `chartPullbackStraightPath` requires for
its two endpoints.

Discharge route (Increment 9): apply `lebesgue_number_lemma_of_metric` to the
*refined* open cover of `X` whose member `V x` is the intersection of
`(chartAt ℂ x).source` with the chart-coord ball preimage. The ball radius
per `x` comes from `exists_ballShaped_chartAt`. The partition assembly then
mirrors `exists_uniform_chart_partition` line by line. -/
lemma exists_uniform_chart_partition_with_ball
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (γ : C(unitInterval, X)) :
    ∃ (n : ℕ) (_ : 0 < n) (pickChart : Fin n → X)
      (radius : Fin n → ℝ),
      (∀ i, 0 < radius i) ∧
      (∀ i, Metric.ball ((chartAt ℂ (pickChart i)) (pickChart i)) (radius i)
              ⊆ (chartAt ℂ (pickChart i)).target) ∧
      (∀ (i : Fin n) (t : unitInterval),
        (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
        γ t ∈ (chartAt ℂ (pickChart i)).source ∧
        (chartAt ℂ (pickChart i)) (γ t) ∈
          Metric.ball ((chartAt ℂ (pickChart i)) (pickChart i)) (radius i)) := by
  -- Step 1: per-chart ball radius. Inlined from
  -- `Jacobian/Periods/PathIntegralViaCoverChartlocal.lean:51`
  -- (`exists_ballShaped_chartAt`); cannot import that file due to a
  -- downstream→upstream build cycle through `PathIntegralViaCoverPick`.
  have hBallShape : ∀ p : X, ∃ r > (0 : ℝ),
      Metric.ball ((chartAt ℂ p) p) r ⊆ (chartAt ℂ p).target := fun p =>
    Metric.isOpen_iff.mp (chartAt ℂ p).open_target ((chartAt ℂ p) p)
      (mem_chart_target ℂ p)
  choose r_picker hr_pos_picker hr_subset_picker using hBallShape
  -- Step 2: refined open cover of X.
  set V : X → Set X := fun x =>
    (chartAt ℂ x).source ∩
      (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) (r_picker x) with hV_def
  have hV_open : ∀ x, IsOpen (V x) := fun x =>
    (chartAt ℂ x).continuousOn.isOpen_inter_preimage
      (chartAt ℂ x).open_source Metric.isOpen_ball
  have hV_self_mem : ∀ y : X, y ∈ V y := fun y =>
    ⟨mem_chart_source ℂ y, by
      change (chartAt ℂ y) y ∈ Metric.ball ((chartAt ℂ y) y) (r_picker y)
      exact Metric.mem_ball_self (hr_pos_picker y)⟩
  -- Step 3: cover `unitInterval` via `γ ⁻¹' V x`.
  have hCover : (univ : Set unitInterval) ⊆ ⋃ x : X, γ ⁻¹' V x :=
    fun t _ => mem_iUnion.mpr ⟨γ t, hV_self_mem (γ t)⟩
  have hPreimageOpen : ∀ x, IsOpen (γ ⁻¹' V x) :=
    fun x => (hV_open x).preimage γ.continuous
  -- Step 4: Lebesgue δ for the refined cover.
  obtain ⟨δ, δ_pos, hδ⟩ :=
    lebesgue_number_lemma_of_metric isCompact_univ hPreimageOpen hCover
  have hδ' : ∀ t : unitInterval, ∃ x : X, Metric.ball t δ ⊆ γ ⁻¹' V x :=
    fun t => hδ t (mem_univ _)
  choose f hf using hδ'
  -- Step 5: pick `n` with `1 / n < δ`.
  obtain ⟨n, hn⟩ : ∃ n : ℕ+, (1 / (n : ℝ)) < δ :=
    ⟨⟨⌊δ⁻¹⌋₊ + 1, Nat.succ_pos _⟩,
      by simpa using inv_lt_of_inv_lt₀ δ_pos <| Nat.lt_floor_add_one _⟩
  -- Step 6: assemble the partition, mirroring `exists_uniform_chart_partition`.
  refine' ⟨ n, n.pos,
    fun i => f ⟨ (i : ℝ) / n + 1 / (2 * n), _, _ ⟩,
    fun i => r_picker (f ⟨ (i : ℝ) / n + 1 / (2 * n), _, _ ⟩),
    fun i => hr_pos_picker _,
    fun i => hr_subset_picker _,
    fun i t ht₁ ht₂ => hf _ _ ⟩ <;> norm_num at *
  all_goals first
    | positivity
    | (rw [Subtype.dist_eq]; norm_num; refine' abs_lt.mpr ⟨_, _⟩ <;>
        ring_nf at * <;> linarith)
    | nlinarith [show (i : ℝ) + 1 ≤ n from mod_cast Nat.succ_le_of_lt i.2,
        mul_inv_cancel₀ (by positivity : (n : ℝ) ≠ 0),
        div_mul_cancel₀ ((i : ℝ) : ℝ) (by positivity : (n : ℝ) ≠ 0)]

end JacobianChallenge.Periods