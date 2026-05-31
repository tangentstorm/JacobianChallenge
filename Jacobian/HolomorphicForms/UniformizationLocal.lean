import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.OpenMapping

/-!
# Local analytic substrate for genus-zero uniformization

This file packages the one-dimensional chart-ball power-series primitive used
by the local uniformization build.  The central Mathlib input is
`DiffContOnCl.hasFPowerSeriesOnBall`: a complex-valued function that is
continuous on the closed ball and complex differentiable on the open ball has
the Cauchy power series expansion on that ball.

The definitions here are intentionally local and do not depend on the global
genus-zero meromorphic-data route.
-/

open Filter Metric

open scoped Topology

namespace JacobianChallenge.HolomorphicForms

/--
Power-series data for a complex-valued function on a one-dimensional chart
ball.  The `series_expansion` field is deliberately the Cauchy power-series
witness supplied by Mathlib, so later uniformization leaves can use this
package without repeating search through the Cauchy integral API.
-/
structure ChartBallPowerSeries where
  center : ℂ
  radius : NNReal
  radius_pos : 0 < radius
  toFun : ℂ → ℂ
  diffContOnCl : DiffContOnCl ℂ toFun (Metric.ball center (radius : ℝ))
  series_expansion :
    HasFPowerSeriesOnBall toFun (cauchyPowerSeries toFun center radius) center radius

namespace ChartBallPowerSeries

/-- The Cauchy power series attached to the chart-ball package. -/
noncomputable abbrev series (data : ChartBallPowerSeries) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  cauchyPowerSeries data.toFun data.center data.radius

/--
Constructor from Mathlib's closed-ball-continuity/open-ball-differentiability
package.
-/
noncomputable def ofDiffContOnCl
    {c : ℂ} {R : NNReal} {f : ℂ → ℂ}
    (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (Metric.ball c (R : ℝ))) :
    ChartBallPowerSeries where
  center := c
  radius := R
  radius_pos := hR
  toFun := f
  diffContOnCl := hf
  series_expansion :=
    DiffContOnCl.hasFPowerSeriesOnBall (R := R) (c := c) (f := f) hf hR

/--
Standalone provider for the Cauchy power-series expansion on a chart ball.
This is the main theorem later uniformization leaves should import.
-/
theorem hasFPowerSeriesOnBall_of_diffContOnCl
    {c : ℂ} {R : NNReal} {f : ℂ → ℂ}
    (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (Metric.ball c (R : ℝ))) :
    HasFPowerSeriesOnBall f (cauchyPowerSeries f c R) c R :=
  DiffContOnCl.hasFPowerSeriesOnBall (R := R) (c := c) (f := f) hf hR

/-- Projection of the packaged Cauchy power-series expansion. -/
theorem hasFPowerSeriesOnBall (data : ChartBallPowerSeries) :
    HasFPowerSeriesOnBall data.toFun data.series data.center data.radius :=
  data.series_expansion

/--
The packaged Cauchy power-series partial sums converge locally uniformly to
the packaged function on the chart disk.
-/
theorem tendstoLocallyUniformlyOn_partialSum (data : ChartBallPowerSeries) :
    TendstoLocallyUniformlyOn
      (fun n z => data.series.partialSum n (z - data.center))
      data.toFun atTop (Metric.eball data.center data.radius) :=
  data.series_expansion.tendstoLocallyUniformlyOn'

/--
On every strict subdisk of the chart disk, the packaged Cauchy power-series
partial sums converge uniformly to the packaged function.
-/
theorem tendstoUniformlyOn_partialSum_of_lt
    (data : ChartBallPowerSeries) {r : NNReal}
    (hr : (r : ENNReal) < data.radius) :
    TendstoUniformlyOn
      (fun n z => data.series.partialSum n (z - data.center))
      data.toFun atTop (Metric.ball data.center r) :=
  data.series_expansion.tendstoUniformlyOn' hr

/-- Cauchy's derivative estimate for the packaged chart-ball function. -/
theorem norm_cderiv_le_of_sphere_bound
    (data : ChartBallPowerSeries) {z : ℂ} {r M : ℝ}
    (hr : 0 < r)
    (hbound : ∀ w ∈ Metric.sphere z r, ‖data.toFun w‖ ≤ M) :
    ‖Complex.cderiv r data.toFun z‖ ≤ M / r :=
  Complex.norm_cderiv_le hr hbound

/--
On a closed ball contained in the chart ball, Mathlib's circle-integral
derivative agrees with the complex derivative of the packaged function.
-/
theorem cderiv_eq_deriv
    (data : ChartBallPowerSeries) {z : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hclosed :
      Metric.closedBall z r ⊆ Metric.ball data.center (data.radius : ℝ)) :
    Complex.cderiv r data.toFun z = deriv data.toFun z :=
  Complex.cderiv_eq_deriv Metric.isOpen_ball data.diffContOnCl.differentiableOn
    hr hclosed

/-- Cauchy's derivative estimate, stated directly for `deriv`. -/
theorem norm_deriv_le_of_sphere_bound
    (data : ChartBallPowerSeries) {z : ℂ} {r M : ℝ}
    (hr : 0 < r)
    (hclosed :
      Metric.closedBall z r ⊆ Metric.ball data.center (data.radius : ℝ))
    (hbound : ∀ w ∈ Metric.sphere z r, ‖data.toFun w‖ ≤ M) :
    ‖deriv data.toFun z‖ ≤ M / r := by
  rw [← data.cderiv_eq_deriv hr hclosed]
  exact data.norm_cderiv_le_of_sphere_bound hr hbound

/--
Cauchy derivative estimates give a Lipschitz bound on a smaller convex chart
ball, provided every point of the smaller ball admits a Cauchy circle of
radius `cauchyRadius` still inside the chart ball.
-/
theorem norm_image_sub_le_of_cauchy_bound
    (data : ChartBallPowerSeries) {innerRadius cauchyRadius M : ℝ}
    (hcauchy_pos : 0 < cauchyRadius)
    (hclosed :
      ∀ z ∈ Metric.ball data.center innerRadius,
        Metric.closedBall z cauchyRadius ⊆
          Metric.ball data.center (data.radius : ℝ))
    (hbound :
      ∀ z ∈ Metric.ball data.center innerRadius,
        ∀ w ∈ Metric.sphere z cauchyRadius, ‖data.toFun w‖ ≤ M)
    {z w : ℂ}
    (hz : z ∈ Metric.ball data.center innerRadius)
    (hw : w ∈ Metric.ball data.center innerRadius) :
    ‖data.toFun w - data.toFun z‖ ≤ (M / cauchyRadius) * ‖w - z‖ := by
  have hdifferentiable :
      ∀ x ∈ Metric.ball data.center innerRadius,
        DifferentiableAt ℂ data.toFun x := by
    intro x hx
    have hx_chart :
        x ∈ Metric.ball data.center (data.radius : ℝ) :=
      hclosed x hx (Metric.mem_closedBall_self hcauchy_pos.le)
    exact data.diffContOnCl.differentiableOn.differentiableAt
      (Metric.isOpen_ball.mem_nhds hx_chart)
  have hderiv_bound :
      ∀ x ∈ Metric.ball data.center innerRadius,
        ‖deriv data.toFun x‖ ≤ M / cauchyRadius := by
    intro x hx
    exact data.norm_deriv_le_of_sphere_bound hcauchy_pos (hclosed x hx)
      (hbound x hx)
  exact (convex_ball data.center innerRadius).norm_image_sub_le_of_norm_deriv_le
    hdifferentiable hderiv_bound hz hw

/--
Uniform Cauchy bounds on a family of packaged chart-ball functions give a
uniform epsilon-delta equicontinuity estimate on the smaller chart ball.
-/
theorem family_uniform_equicontinuousOn_of_cauchy_bound
    {ι : Type*} (data : ι → ChartBallPowerSeries)
    {center : ℂ} {innerRadius cauchyRadius M : ℝ}
    (hcauchy_pos : 0 < cauchyRadius)
    (hM_nonneg : 0 ≤ M)
    (hcenter : ∀ i, (data i).center = center)
    (hclosed :
      ∀ i z, z ∈ Metric.ball center innerRadius →
        Metric.closedBall z cauchyRadius ⊆
          Metric.ball (data i).center ((data i).radius : ℝ))
    (hbound :
      ∀ i z, z ∈ Metric.ball center innerRadius →
        ∀ w ∈ Metric.sphere z cauchyRadius, ‖(data i).toFun w‖ ≤ M) :
    ∀ ε : ℝ, 0 < ε →
      ∃ η : ℝ, 0 < η ∧
        ∀ i z, z ∈ Metric.ball center innerRadius →
          ∀ w, w ∈ Metric.ball center innerRadius →
            dist w z < η → dist ((data i).toFun w) ((data i).toFun z) < ε := by
  intro ε hε
  let K : ℝ := M / cauchyRadius
  have hK_nonneg : 0 ≤ K := div_nonneg hM_nonneg hcauchy_pos.le
  refine ⟨ε / (K + 1), div_pos hε (by linarith), ?_⟩
  intro i z hz w hw hdist
  have hz_i : z ∈ Metric.ball (data i).center innerRadius := by
    simpa [hcenter i] using hz
  have hw_i : w ∈ Metric.ball (data i).center innerRadius := by
    simpa [hcenter i] using hw
  have hdist_norm : ‖w - z‖ < ε / (K + 1) := by
    simpa [dist_eq_norm] using hdist
  have hLip :
      ‖(data i).toFun w - (data i).toFun z‖ ≤ K * ‖w - z‖ := by
    simpa [K] using
      (data i).norm_image_sub_le_of_cauchy_bound hcauchy_pos
        (fun x hx => hclosed i x (by simpa [hcenter i] using hx))
        (fun x hx => hbound i x (by simpa [hcenter i] using hx))
        hz_i hw_i
  have hmul_lt : K * ‖w - z‖ < ε := by
    calc
      K * ‖w - z‖ ≤ (K + 1) * ‖w - z‖ := by
        nlinarith [hK_nonneg, norm_nonneg (w - z)]
      _ < (K + 1) * (ε / (K + 1)) := by
        exact mul_lt_mul_of_pos_left hdist_norm (by linarith)
      _ = ε := by
        field_simp [show K + 1 ≠ 0 by linarith]
  have hnorm_lt : ‖(data i).toFun w - (data i).toFun z‖ < ε :=
    lt_of_le_of_lt hLip hmul_lt
  simpa [dist_eq_norm] using hnorm_lt

/-- The packaged function is analytic at the center of its chart ball. -/
theorem analyticAt_center (data : ChartBallPowerSeries) :
    AnalyticAt ℂ data.toFun data.center :=
  data.series_expansion.analyticAt

/--
The packaged function is strictly differentiable at the chart center with
derivative `deriv data.toFun data.center`.
-/
theorem hasStrictDerivAt_center (data : ChartBallPowerSeries) :
    HasStrictDerivAt data.toFun (deriv data.toFun data.center) data.center :=
  data.analyticAt_center.hasStrictDerivAt

/--
The inverse-function-theorem local inverse of a packaged chart-ball function
at a center where the derivative is nonzero.
-/
noncomputable def localInverse
    (data : ChartBallPowerSeries)
    (hderiv : deriv data.toFun data.center ≠ 0) : ℂ → ℂ :=
  data.hasStrictDerivAt_center.localInverse data.toFun
    (deriv data.toFun data.center) data.center hderiv

/-- The inverse-function-theorem local inverse is eventually a left inverse. -/
theorem eventually_left_inverse_localInverse
    (data : ChartBallPowerSeries)
    (hderiv : deriv data.toFun data.center ≠ 0) :
    ∀ᶠ z in 𝓝 data.center,
      data.localInverse hderiv (data.toFun z) = z :=
  by
    simpa [localInverse] using
      data.hasStrictDerivAt_center.eventually_left_inverse hderiv

/-- The inverse-function-theorem local inverse is eventually a right inverse. -/
theorem eventually_right_inverse_localInverse
    (data : ChartBallPowerSeries)
    (hderiv : deriv data.toFun data.center ≠ 0) :
    ∀ᶠ w in 𝓝 (data.toFun data.center),
      data.toFun (data.localInverse hderiv w) = w :=
  by
    simpa [localInverse] using
      data.hasStrictDerivAt_center.eventually_right_inverse hderiv

/-- The packaged local inverse is analytic at the image of the chart center. -/
theorem analyticAt_localInverse
    (data : ChartBallPowerSeries)
    (hderiv : deriv data.toFun data.center ≠ 0) :
    AnalyticAt ℂ (data.localInverse hderiv) (data.toFun data.center) :=
  data.analyticAt_center.analyticAt_localInverse hderiv

/--
On a sufficiently small ball around the chart center, a packaged chart-ball
function with nonzero center derivative is injective.  The radius is also
chosen inside the packaged chart radius.
-/
theorem exists_ball_injOn
    (data : ChartBallPowerSeries)
    (hderiv : deriv data.toFun data.center ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ r < (data.radius : ℝ) ∧
      Set.InjOn data.toFun (Metric.ball data.center r) := by
  rcases Metric.mem_nhds_iff.mp
      (data.eventually_left_inverse_localInverse hderiv) with
    ⟨δ, hδ_pos, hδ_subset⟩
  let r : ℝ := min (δ / 2) ((data.radius : ℝ) / 2)
  have hR_pos : 0 < (data.radius : ℝ) := by exact_mod_cast data.radius_pos
  have hr_pos : 0 < r := by
    simp [r, hδ_pos, hR_pos]
  have hr_lt_radius : r < (data.radius : ℝ) := by
    have hr_le : r ≤ (data.radius : ℝ) / 2 := min_le_right _ _
    linarith
  have hr_le_delta : r ≤ δ := by
    have hr_le : r ≤ δ / 2 := min_le_left _ _
    linarith
  refine ⟨r, hr_pos, hr_lt_radius, ?_⟩
  intro z hz w hw hzw
  have hz_delta : z ∈ Metric.ball data.center δ := lt_of_lt_of_le hz hr_le_delta
  have hw_delta : w ∈ Metric.ball data.center δ := lt_of_lt_of_le hw hr_le_delta
  have hz_inv := hδ_subset hz_delta
  have hw_inv := hδ_subset hw_delta
  calc
    z = data.localInverse hderiv (data.toFun z) := hz_inv.symm
    _ = data.localInverse hderiv (data.toFun w) := by rw [hzw]
    _ = w := hw_inv

/-- Concrete local normalized ball data for a packaged chart-ball function. -/
structure LocalNormalizedBallData (data : ChartBallPowerSeries) where
  domainRadius : ℝ
  imageRadius : ℝ
  domainRadius_pos : 0 < domainRadius
  domainRadius_lt_chart : domainRadius < (data.radius : ℝ)
  injOn_ball : Set.InjOn data.toFun (Metric.ball data.center domainRadius)
  imageRadius_pos : 0 < imageRadius
  image_ball_subset :
    Metric.ball (data.toFun data.center) imageRadius ⊆
      data.toFun '' Metric.closedBall data.center domainRadius

/--
Local normalized ball provider: at a nonzero center derivative, the packaged
chart-ball function is injective on a smaller ball and its image contains a
positive ball around the center value.
-/
theorem exists_localNormalizedBallData
    (data : ChartBallPowerSeries)
    (hderiv : deriv data.toFun data.center ≠ 0) :
    Nonempty (LocalNormalizedBallData data) := by
  rcases data.exists_ball_injOn hderiv with ⟨ρ, hρ_pos, hρ_lt, hρ_inj⟩
  let r : ℝ := ρ / 2
  have hr_pos : 0 < r := by positivity
  have hr_lt_ρ : r < ρ := half_lt_self hρ_pos
  have hr_lt_chart : r < (data.radius : ℝ) := hr_lt_ρ.trans hρ_lt
  have hr_le_ρ : r ≤ ρ := hr_lt_ρ.le
  have hinj : Set.InjOn data.toFun (Metric.ball data.center r) :=
    hρ_inj.mono (Metric.ball_subset_ball hr_le_ρ)
  have hsmall : DiffContOnCl ℂ data.toFun (Metric.ball data.center r) :=
    data.diffContOnCl.mono (Metric.ball_subset_ball hr_lt_chart.le)
  have hboundary_ne :
      ∀ z ∈ Metric.sphere data.center r,
        data.toFun z ≠ data.toFun data.center := by
    intro z hz hzeq
    have hz_ball : z ∈ Metric.ball data.center ρ :=
      Metric.sphere_subset_ball hr_lt_ρ hz
    have hc_ball : data.center ∈ Metric.ball data.center ρ :=
      Metric.mem_ball_self hρ_pos
    have hzc : z = data.center := hρ_inj hz_ball hc_ball hzeq
    exact (ne_of_mem_sphere hz hr_pos.ne.symm) hzc
  have hsphere_nonempty : (Metric.sphere data.center r).Nonempty :=
    NormedSpace.sphere_nonempty.mpr hr_pos.le
  have hcont :
      ContinuousOn (fun z => ‖data.toFun z - data.toFun data.center‖)
        (Metric.sphere data.center r) :=
    continuous_norm.comp_continuousOn
      ((hsmall.sub_const (data.toFun data.center)).continuousOn_ball.mono
        Metric.sphere_subset_closedBall)
  obtain ⟨x, hx, hx_min⟩ :=
    (isCompact_sphere data.center r).exists_isMinOn hsphere_nonempty hcont
  let lower : ℝ := ‖data.toFun x - data.toFun data.center‖
  have hlower_pos : 0 < lower := by
    exact norm_sub_pos_iff.mpr (hboundary_ne x hx)
  have hlower_bound :
      ∀ z ∈ Metric.sphere data.center r,
        lower ≤ ‖data.toFun z - data.toFun data.center‖ := by
    intro z hz
    exact hx_min hz
  have hcenter_freq :
      ∃ᶠ z in 𝓝 data.center, data.toFun z ≠ data.toFun data.center := by
    exact ((data.hasStrictDerivAt_center.hasDerivAt.eventually_ne hderiv).frequently.filter_mono
      nhdsWithin_le_nhds)
  refine ⟨LocalNormalizedBallData.mk r (lower / 2) hr_pos hr_lt_chart hinj
    (half_pos hlower_pos) ?_⟩
  exact hsmall.ball_subset_image_closedBall hr_pos hlower_bound hcenter_freq

/--
The inverse-function-theorem open partial homeomorphism attached to a
packaged chart-ball function with nonzero center derivative.
-/
noncomputable def localOpenPartialHomeomorph
    (data : ChartBallPowerSeries)
    (hderiv : deriv data.toFun data.center ≠ 0) :
    OpenPartialHomeomorph ℂ ℂ :=
  (data.hasStrictDerivAt_center.hasStrictFDerivAt_equiv hderiv).toOpenPartialHomeomorph
    data.toFun

/--
Local chart-homeomorphism data around the chart center.  The homeomorphism is
Mathlib's inverse-function-theorem homeomorphism between open source/target
neighborhoods, together with explicit source and target balls contained in
those neighborhoods.
-/
structure LocalNormalizedChartHomeomorphData (data : ChartBallPowerSeries) where
  domainRadius : ℝ
  imageRadius : ℝ
  domainRadius_pos : 0 < domainRadius
  imageRadius_pos : 0 < imageRadius
  domainRadius_lt_chart : domainRadius < (data.radius : ℝ)
  localOpen : OpenPartialHomeomorph ℂ ℂ
  center_mem_source : data.center ∈ localOpen.source
  imageCenter_mem_target : data.toFun data.center ∈ localOpen.target
  source_ball_subset : Metric.ball data.center domainRadius ⊆ localOpen.source
  target_ball_subset : Metric.ball (data.toFun data.center) imageRadius ⊆ localOpen.target
  homeomorph : localOpen.source ≃ₜ localOpen.target
  homeomorph_eq : homeomorph = localOpen.toHomeomorphSourceTarget
  toFun_eq_on_source : ∀ z : localOpen.source, (homeomorph z : ℂ) = data.toFun z
  sourceImageHomeomorph :
    Metric.ball data.center domainRadius ≃ₜ
      (data.toFun '' Metric.ball data.center domainRadius)
  sourceImageHomeomorph_toFun_eq :
    ∀ z : Metric.ball data.center domainRadius,
      (sourceImageHomeomorph z : ℂ) = data.toFun z

/--
Local normalized chart-homeomorphism provider: at a nonzero center derivative,
the inverse function theorem supplies a homeomorphism between open source and
target neighborhoods, and both neighborhoods contain positive metric balls
around the center and center value.
-/
theorem exists_localNormalizedChartHomeomorphData
    (data : ChartBallPowerSeries)
    (hderiv : deriv data.toFun data.center ≠ 0) :
    Nonempty (LocalNormalizedChartHomeomorphData data) := by
  let e := data.localOpenPartialHomeomorph hderiv
  have hsource : data.center ∈ e.source := by
    simpa [e, localOpenPartialHomeomorph] using
      (data.hasStrictDerivAt_center.hasStrictFDerivAt_equiv hderiv).mem_toOpenPartialHomeomorph_source
  have htarget : data.toFun data.center ∈ e.target := by
    simpa [e, localOpenPartialHomeomorph] using
      (data.hasStrictDerivAt_center.hasStrictFDerivAt_equiv hderiv).image_mem_toOpenPartialHomeomorph_target
  rcases Metric.mem_nhds_iff.mp (e.open_source.mem_nhds hsource) with
    ⟨ρ, hρ_pos, hρ_subset⟩
  rcases Metric.mem_nhds_iff.mp (e.open_target.mem_nhds htarget) with
    ⟨η, hη_pos, hη_subset⟩
  let r : ℝ := min (ρ / 2) ((data.radius : ℝ) / 2)
  let s : ℝ := η / 2
  have hR_pos : 0 < (data.radius : ℝ) := by exact_mod_cast data.radius_pos
  have hr_pos : 0 < r := by
    simp [r, hρ_pos, hR_pos]
  have hs_pos : 0 < s := by
    simp [s, hη_pos]
  have hr_lt_chart : r < (data.radius : ℝ) := by
    have hr_le : r ≤ (data.radius : ℝ) / 2 := min_le_right _ _
    linarith
  have hr_le_ρ : r ≤ ρ := by
    have hr_le : r ≤ ρ / 2 := min_le_left _ _
    linarith
  have hs_le_η : s ≤ η := by
    dsimp [s]
    linarith
  have hsource_ball_subset :
      Metric.ball data.center r ⊆ e.source :=
    (Metric.ball_subset_ball hr_le_ρ).trans hρ_subset
  have htarget_ball_subset :
      Metric.ball (data.toFun data.center) s ⊆ e.target :=
    (Metric.ball_subset_ball hs_le_η).trans hη_subset
  have himage :
      e '' Metric.ball data.center r =
        data.toFun '' Metric.ball data.center r := by
    simp [e, localOpenPartialHomeomorph]
  refine ⟨
    { domainRadius := r
      imageRadius := s
      domainRadius_pos := hr_pos
      imageRadius_pos := hs_pos
      domainRadius_lt_chart := hr_lt_chart
      localOpen := e
      center_mem_source := hsource
      imageCenter_mem_target := htarget
      source_ball_subset := hsource_ball_subset
      target_ball_subset := htarget_ball_subset
      homeomorph := e.toHomeomorphSourceTarget
      homeomorph_eq := rfl
      toFun_eq_on_source := ?_
      sourceImageHomeomorph :=
        e.homeomorphOfImageSubsetSource hsource_ball_subset himage
      sourceImageHomeomorph_toFun_eq := ?_ }⟩
  · intro z
    change e z = data.toFun z
    simp [e, localOpenPartialHomeomorph]
  · intro z
    change e z = data.toFun z
    simp [e, localOpenPartialHomeomorph]

/--
Local open-image provider for a packaged chart-ball function.  If the image
displacement is bounded below by `ε` on the boundary sphere and the function
is frequently nonconstant at the center, then the image of the closed chart
ball contains the ball of radius `ε / 2` around the center value.
-/
theorem ball_subset_image_closedBall
    (data : ChartBallPowerSeries) {ε : ℝ}
    (hf :
      ∀ z ∈ Metric.sphere data.center (data.radius : ℝ),
        ε ≤ ‖data.toFun z - data.toFun data.center‖)
    (hcenter : ∃ᶠ z in 𝓝 data.center, data.toFun z ≠ data.toFun data.center) :
    Metric.ball (data.toFun data.center) (ε / 2) ⊆
      data.toFun '' Metric.closedBall data.center (data.radius : ℝ) :=
  data.diffContOnCl.ball_subset_image_closedBall
    (by exact_mod_cast data.radius_pos) hf hcenter

/--
Closed-ball differentiability also supplies a chart-ball power series by
Mathlib's `DifferentiableOn.hasFPowerSeriesOnBall` wrapper.
-/
theorem hasFPowerSeriesOnBall_of_differentiableOn_closedBall
    {c : ℂ} {R : NNReal} {f : ℂ → ℂ}
    (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall c (R : ℝ))) :
    HasFPowerSeriesOnBall f (cauchyPowerSeries f c R) c R :=
  DifferentiableOn.hasFPowerSeriesOnBall (R := R) (c := c) (f := f) hf hR

end ChartBallPowerSeries

end JacobianChallenge.HolomorphicForms
