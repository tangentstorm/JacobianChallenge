import Jacobian.Periods.PathIntegralViaChartCorrect
import Jacobian.Periods.CurveIntegralSubpath
import Jacobian.Periods.ChartedFormPullbackCurveIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option linter.unusedSectionVars false

/-!
# Segment-additivity of `pathIntegralViaChartCorrect`

States that splitting a chart-local corrected path integral at any
parameter `s ∈ [0, 1]` produces the sum of two sub-integrals over
`γ.subpath 0 s` and `γ.subpath s 1`.

## Strategy

1. The chart-lift commutes with `Path.subpath` (Path.ext, near-
   definitional).
2. The `curveIntegral` of a `Path.subpath` agrees with the interval
   integral over the sub-interval (`curveIntegral_subpath_of_le` from
   `CurveIntegralSubpath.lean`, the **single named analytic gap**).
3. `intervalIntegral.integral_add_adjacent_intervals` to combine the
   two sub-integrals into the full one.
-/

namespace JacobianChallenge.Periods

open Set MeasureTheory Path
open scoped unitInterval
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

omit [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X] in
/--
The chart-lift commutes with `Path.subpath`: lifting a subpath
through the chart equals taking the subpath of the chart-lifted
path. Proved by `Path.ext`.
-/
theorem chartLift_subpath
    (c : OpenPartialHomeomorph X E)
    {a b : X} (γ : Path a b) (hrange : range γ ⊆ c.source)
    (t₀ t₁ : unitInterval)
    (hsub : range (γ.subpath t₀ t₁) ⊆ c.source) :
    chartLift c (γ.subpath t₀ t₁) hsub =
      (chartLift c γ hrange).subpath t₀ t₁ := by
  apply Path.ext
  funext s
  rfl


theorem pathIntegralViaChartCorrect_split_subpath
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b) (hrange : range γ ⊆ c.source)
    (s : unitInterval)
    (hsub_left : range (γ.subpath 0 s) ⊆ c.source)
    (hsub_right : range (γ.subpath s 1) ⊆ c.source)
    (hint_left : IntervalIntegrable
      (fun t => (chartedFormPullback c ω) ((chartLift c γ hrange).extend t)
        (derivWithin (chartLift c γ hrange).extend (Set.Icc 0 1) t))
      volume 0 (s : ℝ))
    (hint_right : IntervalIntegrable
      (fun t => (chartedFormPullback c ω) ((chartLift c γ hrange).extend t)
        (derivWithin (chartLift c γ hrange).extend (Set.Icc 0 1) t))
      volume (s : ℝ) 1) :
    pathIntegralViaChartCorrect c ω γ hrange =
      pathIntegralViaChartCorrect c ω (γ.subpath 0 s) hsub_left +
      pathIntegralViaChartCorrect c ω (γ.subpath s 1) hsub_right := by
  -- Notation: gtilde for the chart-lifted full path, omtilde for the chart-pullback form.
  set gtilde := chartLift c γ hrange with hgtilde
  set omtilde := chartedFormPullback c ω with homtilde
  -- Bridge: the integrand `fun t => omtilde (gtilde.extend t) (derivWithin ...)` equals
  -- `curveIntegralFun omtilde gtilde` (by definition of the latter).
  have h_fun_eq :
      (fun t => omtilde (gtilde.extend t)
        (derivWithin gtilde.extend (Set.Icc 0 1) t))
      = curveIntegralFun omtilde gtilde := by
    funext t
    rw [curveIntegralFun_def]
  -- Convert the integrability hypotheses into `curveIntegralFun` form.
  have hint_left' : IntervalIntegrable
      (curveIntegralFun omtilde gtilde) volume 0 (s : ℝ) := h_fun_eq ▸ hint_left
  have hint_right' : IntervalIntegrable
      (curveIntegralFun omtilde gtilde) volume (s : ℝ) 1 := h_fun_eq ▸ hint_right
  -- Unfold the LHS to curveIntegral, then to an interval integral on [0,1].
  show curveIntegral omtilde gtilde = _ + _
  rw [curveIntegral_def]
  -- Split at t = s via `intervalIntegral.integral_add_adjacent_intervals`.
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (0 : ℝ)) (b := (s : ℝ)) (c := (1 : ℝ)) hint_left' hint_right']
  -- Now identify each interval-integral piece with the corresponding
  -- pathIntegralViaChartCorrect of the subpath.
  congr 1
  · -- left half
    show (∫ t in (0 : ℝ)..(s : ℝ), curveIntegralFun omtilde gtilde t) =
      pathIntegralViaChartCorrect c ω (γ.subpath 0 s) hsub_left
    show (∫ t in (0 : ℝ)..(s : ℝ), curveIntegralFun omtilde gtilde t) =
      curveIntegral omtilde (chartLift c (γ.subpath 0 s) hsub_left)
    rw [chartLift_subpath c γ hrange 0 s hsub_left]
    rw [curveIntegral_subpath_of_le omtilde gtilde 0 s s.2.1]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [curveIntegralFun_def]
  · -- right half
    show (∫ t in (s : ℝ)..1, curveIntegralFun omtilde gtilde t) =
      pathIntegralViaChartCorrect c ω (γ.subpath s 1) hsub_right
    show (∫ t in (s : ℝ)..1, curveIntegralFun omtilde gtilde t) =
      curveIntegral omtilde (chartLift c (γ.subpath s 1) hsub_right)
    rw [chartLift_subpath c γ hrange s 1 hsub_right]
    rw [curveIntegral_subpath_of_le omtilde gtilde s 1 s.2.2]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [curveIntegralFun_def]

end JacobianChallenge.Periods
