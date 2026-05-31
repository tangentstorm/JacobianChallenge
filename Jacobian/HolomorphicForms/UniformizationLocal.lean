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

/-- The packaged function is analytic at the center of its chart ball. -/
theorem analyticAt_center (data : ChartBallPowerSeries) :
    AnalyticAt ℂ data.toFun data.center :=
  data.series_expansion.analyticAt

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
