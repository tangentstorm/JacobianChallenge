import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Complex
import Mathlib.Topology.MetricSpace.Basic

/-!
# Continuous bump functions on a `ChartedSpace ℂ`

This file provides a continuous, real-valued bump function on a complex
1-manifold `X`, supported in a single chart and equal to 1 in a neighbourhood
of any chosen base point `Q : X`.

Mathlib's `SmoothBumpFunction` is parametrised by a model with corners over
`ℝ`, so it does not directly apply to `[IsManifold (modelWithCornersSelf ℂ ℂ)
⊤ X]` (whose model is over `ℂ`). We build the bump from
`ContDiffBump`-on-`ℂ` (which works over any normed space over `ℝ`, including
`ℂ`) plus the chart at `Q`, extending by zero off the chart source.

The exported facts are the interface that the honest single-pole-lift
construction in `SinglePoleLift.lean` consumes:

* `cMfldBump_apply_self : cMfldBump Q Q = 1`
* `cMfldBump_eq_zero_off_chartSource : ∀ x ∉ (chartAt ℂ Q).source, cMfldBump Q x = 0`
* `cMfldBump_eq_one_near : ∃ U open, Q ∈ U, ∀ x ∈ U, cMfldBump Q x = 1`
* `cMfldBump_le_one`, `cMfldBump_nonneg`
* `cMfldBump_continuous` — requires `[T2Space X]`, used to identify
  the compact pulled-back support `φ.symm '' closedBall` with a closed
  set whose complement is a zero-neighbourhood of any point off-chart.

The interface only needs `[ChartedSpace ℂ X]` (continuity additionally
needs `[T2Space X]`); no `IsManifold` instance is required since this
file works at the topological-chart level.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-! ### Auxiliary: a positive radius around the chart image of `Q` whose
open ball lies inside the chart target. -/

/-- A radius witnessing that some open ball around the chart image of `Q`
fits entirely inside the chart target. -/
private noncomputable def chartBallRadius (Q : X) : ℝ :=
  Classical.choose <| Metric.isOpen_iff.mp (chartAt ℂ Q).open_target
    ((chartAt ℂ Q) Q) ((chartAt ℂ Q).map_source (mem_chart_source ℂ Q))

private theorem chartBallRadius_pos (Q : X) : 0 < chartBallRadius Q :=
  (Classical.choose_spec <| Metric.isOpen_iff.mp (chartAt ℂ Q).open_target
    ((chartAt ℂ Q) Q) ((chartAt ℂ Q).map_source (mem_chart_source ℂ Q))).1

private theorem chartBallRadius_ball_subset_target (Q : X) :
    Metric.ball ((chartAt ℂ Q) Q) (chartBallRadius Q) ⊆ (chartAt ℂ Q).target :=
  (Classical.choose_spec <| Metric.isOpen_iff.mp (chartAt ℂ Q).open_target
    ((chartAt ℂ Q) Q) ((chartAt ℂ Q).map_source (mem_chart_source ℂ Q))).2

/-! ### The bump-function building block: a `ContDiffBump` in `ℂ`. -/

/-- The chart-local bump on `ℂ`.  Inner radius `chartBallRadius Q / 4`,
outer radius `chartBallRadius Q / 2`; the closed ball of the outer radius
sits inside the open `chartBallRadius`-ball, hence inside the chart target. -/
private noncomputable def cMfldBumpKernel (Q : X) :
    ContDiffBump ((chartAt ℂ Q) Q) where
  rIn := chartBallRadius Q / 4
  rOut := chartBallRadius Q / 2
  rIn_pos := by have := chartBallRadius_pos Q; linarith
  rIn_lt_rOut := by have := chartBallRadius_pos Q; linarith

private theorem cMfldBumpKernel_rOut_eq (Q : X) :
    (cMfldBumpKernel Q).rOut = chartBallRadius Q / 2 := rfl

private theorem cMfldBumpKernel_rIn_eq (Q : X) :
    (cMfldBumpKernel Q).rIn = chartBallRadius Q / 4 := rfl

/-- Closed ball of the outer radius is inside the chart target. -/
private theorem cMfldBumpKernel_closedBall_subset_target (Q : X) :
    Metric.closedBall ((chartAt ℂ Q) Q) (cMfldBumpKernel Q).rOut ⊆ (chartAt ℂ Q).target := by
  intro y hy
  apply chartBallRadius_ball_subset_target Q
  rw [Metric.mem_closedBall, cMfldBumpKernel_rOut_eq] at hy
  rw [Metric.mem_ball]
  have := chartBallRadius_pos Q
  linarith

/-! ### The bump on `X`. -/

/-- The chart-local continuous bump on `X` centered at `Q`.

* `1` in a neighbourhood of `Q` (specifically on the inner ball of
  `cMfldBumpKernel Q`, pulled back through the chart);
* `0` off the chart source.

Continuity follows from continuity of the chart on its source plus the fact
that the bump kernel vanishes outside the closed outer ball, which itself
sits inside the chart target. -/
noncomputable def cMfldBump (Q : X) : X → ℝ := fun x =>
  haveI : Decidable (x ∈ (chartAt ℂ Q).source) := Classical.dec _
  if _ : x ∈ (chartAt ℂ Q).source then
    (cMfldBumpKernel Q : ℂ → ℝ) ((chartAt ℂ Q) x)
  else 0

/-! ### The five exported lemmas. -/

theorem cMfldBump_apply_self (Q : X) : cMfldBump Q Q = 1 := by
  unfold cMfldBump
  rw [dif_pos (mem_chart_source ℂ Q)]
  refine (cMfldBumpKernel Q).one_of_mem_closedBall ?_
  rw [Metric.mem_closedBall, dist_self]
  exact le_of_lt (cMfldBumpKernel Q).rIn_pos

theorem cMfldBump_eq_zero_off_chartSource (Q : X) :
    ∀ x : X, x ∉ (chartAt ℂ Q).source → cMfldBump Q x = 0 := by
  intro x hx
  unfold cMfldBump
  rw [dif_neg hx]

theorem cMfldBump_le_one (Q : X) (x : X) : cMfldBump Q x ≤ 1 := by
  unfold cMfldBump
  by_cases hx : x ∈ (chartAt ℂ Q).source
  · rw [dif_pos hx]; exact (cMfldBumpKernel Q).le_one
  · rw [dif_neg hx]; norm_num

theorem cMfldBump_nonneg (Q : X) (x : X) : 0 ≤ cMfldBump Q x := by
  unfold cMfldBump
  by_cases hx : x ∈ (chartAt ℂ Q).source
  · rw [dif_pos hx]; exact (cMfldBumpKernel Q).nonneg
  · rw [dif_neg hx]

theorem cMfldBump_eq_one_near (Q : X) :
    ∃ U : Set X, IsOpen U ∧ Q ∈ U ∧ ∀ x ∈ U, cMfldBump Q x = 1 := by
  -- U := source ∩ chart⁻¹(ball (chart Q) rIn).
  set φ := chartAt ℂ Q with hφ
  set kernel := cMfldBumpKernel Q with hkernel
  refine ⟨φ.source ∩ φ ⁻¹' Metric.ball (φ Q) kernel.rIn, ?_, ?_, ?_⟩
  · -- Open
    refine φ.continuousOn_toFun.isOpen_inter_preimage φ.open_source Metric.isOpen_ball
  · -- Q is in U
    refine ⟨mem_chart_source ℂ Q, ?_⟩
    show φ Q ∈ Metric.ball (φ Q) kernel.rIn
    simpa [Metric.mem_ball, dist_self] using kernel.rIn_pos
  · -- All points of U give bump value 1
    intro x ⟨hxsrc, hxball⟩
    unfold cMfldBump
    rw [dif_pos hxsrc]
    refine kernel.one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall]
    have : (φ : X → ℂ) x ∈ Metric.ball (φ Q) kernel.rIn := hxball
    rw [Metric.mem_ball] at this
    linarith

theorem cMfldBump_continuous [T2Space X] (Q : X) : Continuous (cMfldBump (X := X) Q) := by
  set φ := chartAt ℂ Q with hφ
  set kernel := cMfldBumpKernel Q with hkernel
  -- Key compact set: K_X := φ.symm '' closedBall (φ Q) kernel.rOut.
  -- It's compact (continuous image of a compact closedBall), hence closed in T2 X.
  -- Outside K_X, cMfldBump is 0; inside (and inside source), cMfldBump = kernel ∘ φ.
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ φ.source
  · -- ContinuousAt on source: agrees with kernel ∘ φ near x.
    have hsrc_open : IsOpen φ.source := φ.open_source
    refine ContinuousAt.congr (f := fun y => kernel ((φ : X → ℂ) y)) ?_ ?_
    · refine kernel.continuous.continuousAt.comp ?_
      exact (φ.continuousOn_toFun.continuousAt (hsrc_open.mem_nhds hx))
    · filter_upwards [hsrc_open.mem_nhds hx] with y hy
      unfold cMfldBump
      rw [dif_pos hy]
  · -- x ∉ source. Show eventually-zero in a neighborhood.
    -- Build a closed set K_X ⊆ source where the bump is potentially nonzero;
    -- show x ∉ K_X; then K_X^c is an open nbhd of x where bump = 0.
    set K_target : Set ℂ := Metric.closedBall (φ Q) kernel.rOut with hK_target
    have hK_target_subset : K_target ⊆ φ.target :=
      cMfldBumpKernel_closedBall_subset_target Q
    have hK_target_compact : IsCompact K_target := isCompact_closedBall _ _
    set K_X : Set X := φ.symm '' K_target with hK_X
    have hK_X_compact : IsCompact K_X :=
      hK_target_compact.image_of_continuousOn (φ.continuousOn_invFun.mono hK_target_subset)
    have hK_X_closed : IsClosed K_X := hK_X_compact.isClosed
    have hK_X_subset_source : K_X ⊆ φ.source := by
      intro y hy
      obtain ⟨z, hz_in, hzy⟩ := hy
      rw [← hzy]
      exact φ.map_target (hK_target_subset hz_in)
    have hx_notin_K : x ∉ K_X := fun h => hx (hK_X_subset_source h)
    -- Open nbhd: K_Xᶜ.
    have hKc_open : IsOpen K_Xᶜ := hK_X_closed.isOpen_compl
    refine ContinuousAt.congr (f := fun _ : X => (0 : ℝ)) continuousAt_const ?_
    -- Eventually cMfldBump = 0 in 𝓝 x. We use K_Xᶜ ∈ 𝓝 x.
    filter_upwards [hKc_open.mem_nhds hx_notin_K] with y hy
    -- We need (fun _ => 0) y = cMfldBump Q y, i.e., 0 = cMfldBump Q y.
    show (0 : ℝ) = cMfldBump Q y
    -- y ∉ K_X. Cases:
    by_cases hy_src : y ∈ φ.source
    · -- y ∈ source, y ∉ K_X. Show φ y ∉ closedBall (so kernel(φ y) = 0).
      unfold cMfldBump
      rw [dif_pos hy_src]
      symm
      refine kernel.zero_of_le_dist ?_
      -- rOut ≤ dist (φ y) (φ Q).
      by_contra h_lt
      push_neg at h_lt
      apply hy
      refine ⟨φ y, ?_, φ.left_inv hy_src⟩
      rw [hK_target, Metric.mem_closedBall]
      exact le_of_lt h_lt
    · -- y ∉ source: bump = 0 by definition.
      unfold cMfldBump
      rw [dif_neg hy_src]

end JacobianChallenge.HolomorphicForms
