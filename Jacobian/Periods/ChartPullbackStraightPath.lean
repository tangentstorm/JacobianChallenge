import Jacobian.Periods.PathIntegralViaCoverChartlocal
import Jacobian.Periods.PiecewiseC1Path
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.Convex.Basic

/-!
# Chart-pullback straight path

For a Riemann surface `X` (modeled on `ℂ`) and a point `p : X` with a
ball-shaped chart neighborhood, the "chart-pullback straight path"
from `p` to a nearby `x` (with `chartAt ℂ p x ∈ ball`) is the lift
through `(chartAt ℂ p).symm` of the Euclidean straight segment from
`chartAt ℂ p p` to `chartAt ℂ p x` in the ball.

## API

* `chartPullbackStraightPath p x r hr_pos hr_subset hx` — the path itself.
* `chartPullbackStraightPath_chartImage_eq` — `chartAt p (path t) = seg t`.
* `chartPullbackStraightPath_image_in_ball` — chart image stays in ball.
* `chartPullbackStraightPath_range_subset_source` — range in chart.source.
* `chartAt_preimage_ball_mem_nhds` — preimage of ball is a 𝓝 p neighborhood.
-/

namespace JacobianChallenge.Periods

set_option linter.unusedSectionVars false

open Set unitInterval
open scoped Topology

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]

/-- **Chart preimage of ball is a 𝓝 p neighborhood.** -/
theorem chartAt_preimage_ball_mem_nhds (p : X) (r : ℝ) (hr_pos : 0 < r) :
    (chartAt ℂ p) ⁻¹' Metric.ball ((chartAt ℂ p) p) r ∩ (chartAt ℂ p).source ∈ 𝓝 p := by
  have h_chart_continuousAt : ContinuousAt (chartAt ℂ p) p :=
    ((chartAt ℂ p).continuousOn).continuousAt
      ((chartAt ℂ p).open_source.mem_nhds (mem_chart_source ℂ p))
  have h_ball_nhd : Metric.ball ((chartAt ℂ p) p) r ∈ 𝓝 ((chartAt ℂ p) p) :=
    Metric.ball_mem_nhds _ hr_pos
  have h_preim : (chartAt ℂ p) ⁻¹' Metric.ball ((chartAt ℂ p) p) r ∈ 𝓝 p :=
    h_chart_continuousAt.preimage_mem_nhds h_ball_nhd
  exact Filter.inter_mem h_preim
    ((chartAt ℂ p).open_source.mem_nhds (mem_chart_source ℂ p))

/-- The Euclidean straight segment in ℂ from `c p` to `c x`. -/
private noncomputable def chartSegment (p x : X) (t : ℝ) : ℂ :=
  ((1 - t : ℝ) : ℂ) • ((chartAt ℂ p) p) + ((t : ℝ) : ℂ) • ((chartAt ℂ p) x)

@[simp] private theorem chartSegment_zero (p x : X) :
    chartSegment p x 0 = (chartAt ℂ p) p := by
  simp [chartSegment]

@[simp] private theorem chartSegment_one (p x : X) :
    chartSegment p x 1 = (chartAt ℂ p) x := by
  simp [chartSegment]

private theorem chartSegment_continuous (p x : X) : Continuous (chartSegment p x) := by
  unfold chartSegment
  refine Continuous.add ?_ ?_
  · exact (Complex.continuous_ofReal.comp
      (continuous_const.sub continuous_id)).smul continuous_const
  · exact (Complex.continuous_ofReal.comp continuous_id).smul continuous_const

/-- The chart-segment stays in the ball (convexity of the ball). -/
private theorem chartSegment_mem_ball
    (p x : X) (r : ℝ) (hr_pos : 0 < r)
    (hx : (chartAt ℂ p) x ∈ Metric.ball ((chartAt ℂ p) p) r)
    {t : ℝ} (ht : t ∈ unitInterval) :
    chartSegment p x t ∈ Metric.ball ((chartAt ℂ p) p) r := by
  have h_convex : Convex ℝ (Metric.ball ((chartAt ℂ p) p) r) := convex_ball _ _
  have hp : (chartAt ℂ p) p ∈ Metric.ball ((chartAt ℂ p) p) r := Metric.mem_ball_self hr_pos
  rcases ht with ⟨ht0, ht1⟩
  show ((1 - t : ℝ) : ℂ) • ((chartAt ℂ p) p) + ((t : ℝ) : ℂ) • ((chartAt ℂ p) x)
        ∈ Metric.ball ((chartAt ℂ p) p) r
  have h_real_smul :
      ((1 - t : ℝ) : ℂ) • ((chartAt ℂ p) p) + ((t : ℝ) : ℂ) • ((chartAt ℂ p) x)
        = (1 - t) • ((chartAt ℂ p) p) + t • ((chartAt ℂ p) x) := by
    simp [Complex.real_smul]
  rw [h_real_smul]
  exact h_convex hp hx (by linarith) ht0 (by linarith)

/-- **The chart-pullback straight path.**

Requires `x ∈ chart.source` (in addition to `chart x ∈ ball`) so that
`chart.symm (chart x) = x` by `left_inv`. -/
noncomputable def chartPullbackStraightPath
    (p x : X) (r : ℝ) (hr_pos : 0 < r)
    (hr_subset : Metric.ball ((chartAt ℂ p) p) r ⊆ (chartAt ℂ p).target)
    (hx : (chartAt ℂ p) x ∈ Metric.ball ((chartAt ℂ p) p) r)
    (hx_source : x ∈ (chartAt ℂ p).source) :
    Path p x where
  toFun t := (chartAt ℂ p).symm (chartSegment p x t)
  continuous_toFun := by
    have h_seg_cont : Continuous (chartSegment p x) := chartSegment_continuous p x
    have h_symm_cont : ContinuousOn (chartAt ℂ p).symm (chartAt ℂ p).target :=
      (chartAt ℂ p).continuousOn_symm
    refine ContinuousOn.comp_continuous h_symm_cont
      (h_seg_cont.comp continuous_subtype_val) ?_
    intro t
    apply hr_subset
    exact chartSegment_mem_ball p x r hr_pos hx t.2
  source' := by
    show (chartAt ℂ p).symm (chartSegment p x 0) = p
    rw [chartSegment_zero]
    exact (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
  target' := by
    show (chartAt ℂ p).symm (chartSegment p x 1) = x
    rw [chartSegment_one]
    exact (chartAt ℂ p).left_inv hx_source

@[simp] theorem chartPullbackStraightPath_zero
    (p x : X) (r : ℝ) (hr_pos : 0 < r)
    (hr_subset : Metric.ball ((chartAt ℂ p) p) r ⊆ (chartAt ℂ p).target)
    (hx : (chartAt ℂ p) x ∈ Metric.ball ((chartAt ℂ p) p) r)
    (hx_source : x ∈ (chartAt ℂ p).source) :
    chartPullbackStraightPath p x r hr_pos hr_subset hx hx_source 0 = p :=
  (chartPullbackStraightPath p x r hr_pos hr_subset hx hx_source).source'

@[simp] theorem chartPullbackStraightPath_one
    (p x : X) (r : ℝ) (hr_pos : 0 < r)
    (hr_subset : Metric.ball ((chartAt ℂ p) p) r ⊆ (chartAt ℂ p).target)
    (hx : (chartAt ℂ p) x ∈ Metric.ball ((chartAt ℂ p) p) r)
    (hx_source : x ∈ (chartAt ℂ p).source) :
    chartPullbackStraightPath p x r hr_pos hr_subset hx hx_source 1 = x :=
  (chartPullbackStraightPath p x r hr_pos hr_subset hx hx_source).target'

/-- chart-image of chart-pullback straight path = chart segment. -/
theorem chartPullbackStraightPath_chartImage_eq
    (p x : X) (r : ℝ) (hr_pos : 0 < r)
    (hr_subset : Metric.ball ((chartAt ℂ p) p) r ⊆ (chartAt ℂ p).target)
    (hx : (chartAt ℂ p) x ∈ Metric.ball ((chartAt ℂ p) p) r)
    (hx_source : x ∈ (chartAt ℂ p).source)
    (t : unitInterval) :
    (chartAt ℂ p) (chartPullbackStraightPath p x r hr_pos hr_subset hx hx_source t)
      = chartSegment p x t := by
  show (chartAt ℂ p) ((chartAt ℂ p).symm (chartSegment p x t)) = chartSegment p x t
  apply (chartAt ℂ p).right_inv
  apply hr_subset
  exact chartSegment_mem_ball p x r hr_pos hx t.2

/-- chart-image of chart-pullback straight path stays in ball. -/
theorem chartPullbackStraightPath_image_in_ball
    (p x : X) (r : ℝ) (hr_pos : 0 < r)
    (hr_subset : Metric.ball ((chartAt ℂ p) p) r ⊆ (chartAt ℂ p).target)
    (hx : (chartAt ℂ p) x ∈ Metric.ball ((chartAt ℂ p) p) r)
    (hx_source : x ∈ (chartAt ℂ p).source)
    (t : unitInterval) :
    (chartAt ℂ p) (chartPullbackStraightPath p x r hr_pos hr_subset hx hx_source t)
      ∈ Metric.ball ((chartAt ℂ p) p) r := by
  rw [chartPullbackStraightPath_chartImage_eq]
  exact chartSegment_mem_ball p x r hr_pos hx t.2

/-- Range of chart-pullback straight path is in `chart.source`. -/
theorem chartPullbackStraightPath_range_subset_source
    (p x : X) (r : ℝ) (hr_pos : 0 < r)
    (hr_subset : Metric.ball ((chartAt ℂ p) p) r ⊆ (chartAt ℂ p).target)
    (hx : (chartAt ℂ p) x ∈ Metric.ball ((chartAt ℂ p) p) r)
    (hx_source : x ∈ (chartAt ℂ p).source) :
    Set.range (chartPullbackStraightPath p x r hr_pos hr_subset hx hx_source) ⊆ (chartAt ℂ p).source := by
  rintro y ⟨t, rfl⟩
  show (chartAt ℂ p).symm (chartSegment p x t) ∈ (chartAt ℂ p).source
  apply (chartAt ℂ p).map_target
  exact hr_subset (chartSegment_mem_ball p x r hr_pos hx t.2)

/-- **Chart-pullback straight path is chart-C¹** (`IsChartContDiffPath`).

For every chart `chartAt ℂ q : OpenPartialHomeomorph X ℂ` on the
manifold X, the chart-pulled-back composition
`(chartAt ℂ q) ∘ chartPullbackStraightPath.extend` is `ContDiffOn ℝ 1`
on the preimage of `(chartAt ℂ q).source` intersected with `Icc 0 1`.

Proof structure: on `Icc 0 1`, `γ.extend t = (chartAt ℂ p).symm
(chartSegment p x t)` by construction. So
`(chartAt ℂ q) ∘ γ.extend` equals the composition of (a) the chart
transition `(chartAt ℂ q) ∘ (chartAt ℂ p).symm` (which is `ContDiffOn ℂ ⊤`
on its domain by the `[IsManifold]` instance, hence `ContDiffOn ℝ ⊤`
via `ContDiffOn.restrict_scalars`) with (b) the explicit affine
function `chartSegment p x` (which is `ContDiff ℝ ⊤` as a real-linear
combination of complex constants). Composition gives `ContDiffOn ℝ ⊤`
on the preimage; dropping to `1` finishes. -/
theorem chartPullbackStraightPath_isChartContDiffPath
    (p x : X) (r : ℝ) (hr_pos : 0 < r)
    (hr_subset : Metric.ball ((chartAt ℂ p) p) r ⊆ (chartAt ℂ p).target)
    (hx : (chartAt ℂ p) x ∈ Metric.ball ((chartAt ℂ p) p) r)
    (hx_source : x ∈ (chartAt ℂ p).source) :
    JacobianChallenge.TraceDegree.IsChartContDiffPath
      (chartPullbackStraightPath p x r hr_pos hr_subset hx hx_source) := by
  intro q
  set γ := chartPullbackStraightPath p x r hr_pos hr_subset hx hx_source with hγ_def
  set cp := chartAt ℂ p with hcp_def
  set cq := chartAt ℂ q with hcq_def
  -- (1) γ.extend t = cp.symm (chartSegment p x t) for t ∈ Icc 0 1.
  have h_extend_eq : ∀ t ∈ Set.Icc (0:ℝ) 1, γ.extend t = cp.symm (chartSegment p x t) := by
    intro t ht
    rw [γ.extend_extends' ⟨t, (ht : t ∈ unitInterval)⟩]
    rfl
  -- (2) chartSegment is ContDiff ℝ ⊤ as a function ℝ → ℂ.
  have h_seg_contDiff : ContDiff ℝ (⊤ : WithTop ℕ∞) (chartSegment p x) := by
    unfold chartSegment
    have h_ofR : ContDiff ℝ (⊤ : WithTop ℕ∞) (Complex.ofRealCLM : ℝ → ℂ) :=
      Complex.ofRealCLM.contDiff
    have h1 : ContDiff ℝ (⊤ : WithTop ℕ∞)
        (fun t : ℝ => ((1 - t : ℝ) : ℂ) • ((chartAt ℂ p) p)) :=
      (h_ofR.comp (contDiff_const.sub contDiff_id)).smul contDiff_const
    have h2 : ContDiff ℝ (⊤ : WithTop ℕ∞)
        (fun t : ℝ => ((t : ℝ) : ℂ) • ((chartAt ℂ p) x)) :=
      (h_ofR.comp contDiff_id).smul contDiff_const
    exact h1.add h2
  -- (3) chartSegment maps Icc 0 1 into cp.target (via the ball + hr_subset).
  have h_seg_mapsTo_target : ∀ t ∈ Set.Icc (0:ℝ) 1, chartSegment p x t ∈ cp.target :=
    fun t ht => hr_subset (chartSegment_mem_ball p x r hr_pos hx ht)
  -- (4) Chart transition cq ∘ cp.symm is ContMDiffOn 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ⊤ on
  -- D := cp.target ∩ cp.symm⁻¹' cq.source.
  have h_cp_symm : ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) cp.symm cp.target :=
    contMDiffOn_chart_symm
  have h_cq : ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) cq cq.source :=
    contMDiffOn_chart
  set D_trans := cp.target ∩ cp.symm ⁻¹' cq.source with hD_def
  have h_trans_mdiff : ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) (cq ∘ cp.symm) D_trans := by
    have h_cp_symm_restrict : ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (⊤ : WithTop ℕ∞) cp.symm D_trans :=
      h_cp_symm.mono Set.inter_subset_left
    refine h_cq.comp h_cp_symm_restrict ?_
    intro z hz
    exact hz.2
  -- (5) Convert ContMDiffOn 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ⊤ → ContDiffOn ℂ ⊤ via self-model iff.
  have h_trans_contDiffℂ : ContDiffOn ℂ (⊤ : WithTop ℕ∞) (cq ∘ cp.symm) D_trans :=
    contMDiffOn_iff_contDiffOn.mp h_trans_mdiff
  -- (6) Restrict scalars to ℝ.
  have h_trans_contDiffℝ : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (cq ∘ cp.symm) D_trans :=
    h_trans_contDiffℂ.restrict_scalars ℝ
  -- (7) Compose with chartSegment to get ContDiffOn ℝ ⊤ on the preimage chartSegment⁻¹' D_trans.
  have h_lift_contDiff : ContDiffOn ℝ (⊤ : WithTop ℕ∞)
      ((cq ∘ cp.symm) ∘ chartSegment p x) (chartSegment p x ⁻¹' D_trans) := by
    refine h_trans_contDiffℝ.comp h_seg_contDiff.contDiffOn ?_
    intro t ht
    exact ht
  -- (8) Subset: γ.extend⁻¹' cq.source ∩ Icc 0 1 ⊆ chartSegment p x⁻¹' D_trans.
  have h_subset : γ.extend ⁻¹' cq.source ∩ Set.Icc (0:ℝ) 1 ⊆ chartSegment p x ⁻¹' D_trans := by
    intro t ⟨h_pre, h_Icc⟩
    refine ⟨h_seg_mapsTo_target t h_Icc, ?_⟩
    show cp.symm (chartSegment p x t) ∈ cq.source
    rw [← h_extend_eq t h_Icc]
    exact h_pre
  -- (9) Mono to the smaller set.
  have h_target_pre : ContDiffOn ℝ (⊤ : WithTop ℕ∞)
      ((cq ∘ cp.symm) ∘ chartSegment p x)
      (γ.extend ⁻¹' cq.source ∩ Set.Icc (0:ℝ) 1) :=
    h_lift_contDiff.mono h_subset
  -- (10) Congr: swap composition for (cq ∘ γ.extend).
  have h_target_top : ContDiffOn ℝ (⊤ : WithTop ℕ∞) ((cq : X → ℂ) ∘ γ.extend)
      (γ.extend ⁻¹' cq.source ∩ Set.Icc (0:ℝ) 1) := by
    refine h_target_pre.congr ?_
    intro t ⟨_, h_Icc⟩
    show cq (γ.extend t) = cq (cp.symm (chartSegment p x t))
    rw [h_extend_eq t h_Icc]
  -- (11) Drop ⊤ to 1.
  exact h_target_top.of_le (le_top : (1 : WithTop ℕ∞) ≤ ⊤)

end JacobianChallenge.Periods
