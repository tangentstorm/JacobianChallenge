import Jacobian.HolomorphicForms.MontelDiagonalExtraction
import Jacobian.HolomorphicForms.UniformizationLocal
import Jacobian.HolomorphicForms.MontelSourceChartCover

open Filter

namespace JacobianChallenge.HolomorphicForms

lemma exists_stage_common_diagonal_subsequence
    {ι : Type*} [Fintype ι]
    (data : ι → ℕ → ChartBallPowerSeries)
    (c : ι → ℂ) (R : ι → ℝ)
    (cauchyRadius : ι → ℝ) (M : ι → ℝ)
    (hcauchy_pos : ∀ i, 0 < cauchyRadius i)
    (hM_nonneg : ∀ i, 0 ≤ M i)
    (hcenter : ∀ i n, (data i n).center = c i)
    (hclosed : ∀ i n (r : ℝ), r < R i → Metric.closedBall (c i) r ⊆ Metric.ball (data i n).center ((data i n).radius : ℝ))
    (hbound : ∀ i n (r : ℝ) (_hr : r < R i) z, z ∈ Metric.ball (c i) r →
      ∀ w ∈ Metric.sphere z (cauchyRadius i), ‖(data i n).toFun w‖ ≤ M i)
    (hcauchy_closed : ∀ i n (r : ℝ) (_hr : r < R i) z, z ∈ Metric.ball (c i) r →
      Metric.closedBall z (cauchyRadius i) ⊆ Metric.ball (data i n).center ((data i n).radius : ℝ))
    (target : ι → Set ℂ)
    (htarget : ∀ i, IsCompact (target i))
    (hrange : ∀ i n (r : ℝ) (hr : r < R i) (z : Metric.closedBall (c i) r),
      (data i n).boundedContinuousOnClosedBall (hclosed i n r hr) z ∈ target i) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i, ∃ limit : ℂ → ℂ,
        TendstoLocallyUniformlyOn (fun k z => (data i (φ k)).toFun z) limit atTop (Metric.ball (c i) (R i)) := by
  have heq : ∀ i (r : ℝ) (hr : r < R i), Equicontinuous
      ((↑) : Set.range (fun n => (data i n).boundedContinuousOnClosedBall (hclosed i n r hr)) → Metric.closedBall (c i) r → ℂ) := by
    intro i r hr
    have r_mid_ex : ∃ r_mid, r < r_mid ∧ r_mid < R i := exists_between hr
    rcases r_mid_ex with ⟨r_mid, hr_mid_lt, hrmid_lt_R⟩
    have h_unif := ChartBallPowerSeries.family_uniform_equicontinuousOn_of_cauchy_bound
      (fun n => data i n) (hcauchy_pos i) (hM_nonneg i) (fun n => hcenter i n)
      (fun n => hcauchy_closed i n r_mid hrmid_lt_R) (fun n => hbound i n r_mid hrmid_lt_R)
    have h_unif2 : UniformEquicontinuous ((↑) : Set.range (fun n => (data i n).boundedContinuousOnClosedBall (hclosed i n r hr)) → Metric.closedBall (c i) r → ℂ) := by
      rw [Metric.uniformEquicontinuous_iff]
      intro ε hε
      rcases h_unif ε hε with ⟨δ, hδ, hF⟩
      use δ, hδ
      intro z w hw ⟨F, hF_mem⟩
      rcases hF_mem with ⟨n, rfl⟩
      have hz_dist : dist (z : ℂ) (c i) ≤ r := z.property
      have hz_in : (z : ℂ) ∈ Metric.ball (c i) r_mid := by
        apply Metric.mem_ball.mpr
        linarith
      have hw_dist : dist (w : ℂ) (c i) ≤ r := w.property
      have hw_in : (w : ℂ) ∈ Metric.ball (c i) r_mid := by
        apply Metric.mem_ball.mpr
        linarith
      have hw_dist_zw : dist (w : ℂ) (z : ℂ) < δ := by
        rw [dist_comm]
        exact hw
      have hF_eval := hF n z hz_in w hw_in hw_dist_zw
      rw [dist_comm]
      exact hF_eval
    exact h_unif2.equicontinuous
  exact exists_diagonal_subseq_tendstoLocallyUniformlyOn_finite data c R hclosed target htarget hrange heq

theorem tendstoLocallyUniformlyOn_F_clause
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    {ι : Type*} [Fintype ι]
    {localPatches : ι → GenusZeroLocalMontelChartPatch}
    (rp : ∀ i, MontelRealizedPatch X (localPatches i))
    (g : ι → ℕ → ℂ → ℂ)
    (F : ℕ → X → OnePoint ℂ)
    (h_conv : ∀ i, TendstoLocallyUniformlyOn (fun n z => g i n z) (localPatches i).chartBall.toFun
        Filter.atTop (Metric.ball (localPatches i).chartBall.center ((localPatches i).chartBall.radius : ℝ)))
    (h_agree : ∀ i n x, x ∈ (rp i).patch.source → (rp i).patch.targetChart (F n x) = g i n ((rp i).realization.sourceChart x)) :
    ∀ i, TendstoLocallyUniformlyOn (fun n x => (rp i).patch.targetChart (F n x)) (rp i).patch.coord
      Filter.atTop (rp i).patch.source := by
  intro i
  have h_coord := tendstoLocallyUniformlyOn_coord_of_chartBall (rp i) (g i) (h_conv i)
  exact h_coord.congr (fun n x hx => (h_agree i n x hx).symm)
