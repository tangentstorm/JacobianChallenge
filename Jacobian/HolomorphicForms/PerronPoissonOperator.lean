import Jacobian.HolomorphicForms.PerronHarnack
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-!
# Poisson operator on chart discs (Perron engine B2 toolbox W3a)

Blueprint: `docs/perron-b2-dirichlet-phase0.md` §3.1/§4, rows W3a–c;
tracking #232, node `lem:stage-dirichlet-harmonic-exists`.

This file defines the Poisson operator `poissonOperator φ c R` — the
circle average of `φ` against `poissonKernel c · z` — and proves the W3a
core: the operator is **harmonic on the open disc** for boundary data `φ`
continuous on the integration circle.  This is the "Dirichlet problem on
a disc, interior half" cell from which the Perron modification (W5) and
the increasing-limit Harnack corollary (W4b, jc11) are built.

Route (as priced): the companion `herglotzTransform` is holomorphic in
the pole variable by differentiation under the interval integral
(`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`),
the Poisson operator is its real part
(`poissonKernel_eq_re_herglotzRieszKernel` +
`ContinuousLinearMap.circleAverage_comp_comm`), and real parts of
analytic functions are harmonic (`AnalyticAt.harmonicAt_re`).

Normalization, positivity, and monotonicity (W3b/W3c) are the follow-up
commit.  Kernel facts on the circle are imported from `PerronHarnack`
(jc11's W4a); nothing from that file is re-proved here.
-/

namespace JacobianChallenge.HolomorphicForms

open Complex InnerProductSpace Metric Real
open scoped Real Topology

/--
The Poisson operator: the circle average of the boundary datum `φ`
against the Poisson kernel with pole `w`.  For `φ` continuous on the
circle this is the harmonic extension of `φ` to the open disc
(`poissonOperator_harmonicOnNhd`); the boundary-limit statement is
deliberately NOT part of the B2 toolbox (pricing row W3d, dropped).
-/
noncomputable def poissonOperator (φ : ℂ → ℝ) (c : ℂ) (R : ℝ) : ℂ → ℝ :=
  fun w => Real.circleAverage (fun z => poissonKernel c w z • φ z) c R

/--
The Herglotz transform: the circle average of `φ` against the
Herglotz–Riesz kernel with pole `w`.  Holomorphic in `w` on the open
disc (`differentiableOn_herglotzTransform`); its real part is the
Poisson operator (`poissonOperator_eq_re_herglotzTransform`).
-/
noncomputable def herglotzTransform (φ : ℂ → ℝ) (c : ℂ) (R : ℝ) : ℂ → ℂ :=
  fun w => Real.circleAverage (fun z => φ z • herglotzRieszKernel c w z) c R

/-! ### Circle/ball separation helpers -/

/--
A point `z` of the integration circle keeps distance at least
`R - ‖w - c‖` from any `w`; stated in the subtraction normal form
`z - c - (w - c)` used by the kernel denominators.
-/
theorem le_norm_sub_sub_of_mem_sphere {c w z : ℂ} {R : ℝ}
    (hz : z ∈ sphere c R) :
    R - ‖w - c‖ ≤ ‖z - c - (w - c)‖ := by
  have hzR : ‖z - c‖ = R := mem_sphere_iff_norm.mp hz
  calc R - ‖w - c‖ = ‖z - c‖ - ‖w - c‖ := by rw [hzR]
    _ ≤ ‖z - c - (w - c)‖ := norm_sub_norm_le _ _

/--
For `z` on the integration circle and `w` in the open ball, the kernel
denominator `z - c - (w - c)` does not vanish.
-/
theorem sub_sub_ne_zero_of_mem_sphere_ball {c w z : ℂ} {R : ℝ}
    (hz : z ∈ sphere c R) (hw : w ∈ ball c R) :
    z - c - (w - c) ≠ 0 := by
  have hwR : ‖w - c‖ < R := mem_ball_iff_norm.mp hw
  intro h0
  have := le_norm_sub_sub_of_mem_sphere (w := w) hz
  rw [h0, norm_zero] at this
  linarith

/-! ### Pole-variable differentiability of the kernel -/

/--
For a fixed circle point `z` with nonvanishing denominator at `w`, the
Herglotz–Riesz kernel is complex-differentiable in the pole variable,
with derivative `2(z - c) / (z - c - (w - c))²`.
-/
theorem hasDerivAt_herglotzRieszKernel_pole {c w z : ℂ}
    (hne : z - c - (w - c) ≠ 0) :
    HasDerivAt (fun w' => herglotzRieszKernel c w' z)
      (2 * (z - c) / (z - c - (w - c)) ^ 2) w := by
  have hnum : HasDerivAt (fun w' : ℂ => z - c + (w' - c)) 1 w := by
    simpa using ((hasDerivAt_id w).sub_const c).const_add (z - c)
  have hden : HasDerivAt (fun w' : ℂ => z - c - (w' - c)) (-1) w := by
    simpa using ((hasDerivAt_id w).sub_const c).const_sub (z - c)
  have h := hnum.div hden hne
  have hfun : (fun w' => herglotzRieszKernel c w' z)
      = fun w' : ℂ => (z - c + (w' - c)) / (z - c - (w' - c)) := by
    funext w'
    rw [herglotzRieszKernel_def]
  rw [hfun]
  convert h using 1
  field_simp
  ring

/-! ### Continuity of the integrand families -/

/--
For a pole `w` off the integration circle's closed complement (i.e.
`w` in the open ball), the Herglotz–Riesz kernel is continuous in the
circle variable on the circle.
-/
theorem continuousOn_herglotzRieszKernel_sphere {c w : ℂ} {R : ℝ}
    (hw : w ∈ ball c R) :
    ContinuousOn (herglotzRieszKernel c w) (sphere c R) := by
  have hfun : herglotzRieszKernel c w
      = fun z => (z - c + (w - c)) / (z - c - (w - c)) := by
    funext z
    rw [herglotzRieszKernel_def]
  rw [hfun]
  exact ContinuousOn.div (by fun_prop) (by fun_prop)
    fun z hz => sub_sub_ne_zero_of_mem_sphere_ball hz hw

/--
The θ-parametrized Herglotz integrand is continuous for any pole in the
open ball.
-/
theorem continuous_herglotz_integrand {φ : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hφ : ContinuousOn φ (sphere c R)) {w : ℂ}
    (hw : w ∈ ball c R) :
    Continuous (fun θ : ℝ =>
      φ (circleMap c R θ) • herglotzRieszKernel c w (circleMap c R θ)) := by
  have hmem : ∀ θ : ℝ, circleMap c R θ ∈ sphere c R :=
    circleMap_mem_sphere c hR.le
  have hφc : Continuous (fun θ : ℝ => φ (circleMap c R θ)) :=
    hφ.comp_continuous (continuous_circleMap c R) hmem
  have hKc : Continuous
      (fun θ : ℝ => herglotzRieszKernel c w (circleMap c R θ)) :=
    (continuousOn_herglotzRieszKernel_sphere hw).comp_continuous
      (continuous_circleMap c R) hmem
  exact hφc.smul hKc

/--
The θ-parametrized pole-derivative integrand is continuous for any pole
in the open ball.
-/
theorem continuous_herglotz_deriv_integrand {φ : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hφ : ContinuousOn φ (sphere c R)) {w : ℂ}
    (hw : w ∈ ball c R) :
    Continuous (fun θ : ℝ => φ (circleMap c R θ) •
      (2 * (circleMap c R θ - c) / (circleMap c R θ - c - (w - c)) ^ 2)) := by
  have hmem : ∀ θ : ℝ, circleMap c R θ ∈ sphere c R :=
    circleMap_mem_sphere c hR.le
  have hφc : Continuous (fun θ : ℝ => φ (circleMap c R θ)) :=
    hφ.comp_continuous (continuous_circleMap c R) hmem
  have hQc : Continuous (fun θ : ℝ =>
      2 * (circleMap c R θ - c) / (circleMap c R θ - c - (w - c)) ^ 2) := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro θ
    exact pow_ne_zero 2
      (sub_sub_ne_zero_of_mem_sphere_ball (hmem θ) hw)
  exact hφc.smul hQc

/-! ### W3a: the Herglotz transform is holomorphic in the pole -/

/--
**W3a, differentiability half.**  For boundary data continuous on the
integration circle, the Herglotz transform is complex-differentiable on
the open disc: differentiation under the interval integral, dominated on
a closed sub-disc by the constant
`M · 2R/(R - r)²`.
-/
theorem differentiableOn_herglotzTransform {φ : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hφ : ContinuousOn φ (sphere c R)) :
    DifferentiableOn ℂ (herglotzTransform φ c R) (ball c R) := by
  intro w₀ hw₀
  apply DifferentiableAt.differentiableWithinAt
  -- circle data bound
  obtain ⟨M, hM⟩ := (isCompact_sphere c R).exists_bound_of_continuousOn hφ
  have hM0 : 0 ≤ M :=
    le_trans (norm_nonneg _) (hM _ (circleMap_mem_sphere c hR.le 0))
  -- intermediate radius
  have hw₀R : ‖w₀ - c‖ < R := mem_ball_iff_norm.mp hw₀
  set r : ℝ := (‖w₀ - c‖ + R) / 2 with hr_def
  have hr₁ : ‖w₀ - c‖ < r := by rw [hr_def]; linarith
  have hr₂ : r < R := by rw [hr_def]; linarith
  have hRr : 0 < R - r := by linarith
  have hball : ∀ w ∈ closedBall c r, w ∈ ball c R := fun w hw =>
    mem_ball_iff_norm.mpr (lt_of_le_of_lt (mem_closedBall_iff_norm.mp hw) hr₂)
  -- denominator control on the closed sub-disc
  have hden : ∀ (θ : ℝ), ∀ w ∈ closedBall c r,
      R - r ≤ ‖circleMap c R θ - c - (w - c)‖ := by
    intro θ w hw
    calc R - r ≤ R - ‖w - c‖ := by
          have := mem_closedBall_iff_norm.mp hw; linarith
      _ ≤ ‖circleMap c R θ - c - (w - c)‖ :=
          le_norm_sub_sub_of_mem_sphere (circleMap_mem_sphere c hR.le θ)
  have hden_ne : ∀ (θ : ℝ), ∀ w ∈ closedBall c r,
      circleMap c R θ - c - (w - c) ≠ 0 := by
    intro θ w hw h0
    have := hden θ w hw
    rw [h0, norm_zero] at this
    linarith
  -- dominated differentiation under the interval integral
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := MeasureTheory.volume) (a := 0) (b := 2 * π)
    (F := fun w θ =>
      φ (circleMap c R θ) • herglotzRieszKernel c w (circleMap c R θ))
    (F' := fun w θ => φ (circleMap c R θ) •
      (2 * (circleMap c R θ - c) / (circleMap c R θ - c - (w - c)) ^ 2))
    (x₀ := w₀) (bound := fun _ => M * (2 * R / (R - r) ^ 2))
    (Filter.mem_of_superset
      (isOpen_ball.mem_nhds (mem_ball_iff_norm.mpr hr₁))
      ball_subset_closedBall)
    (by
      filter_upwards [isOpen_ball.mem_nhds hw₀] with w hw
      exact (continuous_herglotz_integrand hR hφ hw).aestronglyMeasurable)
    ((continuous_herglotz_integrand hR hφ hw₀).intervalIntegrable _ _)
    (continuous_herglotz_deriv_integrand hR hφ hw₀).aestronglyMeasurable
    (Filter.Eventually.of_forall (by
      intro θ _ w hw
      set z : ℂ := circleMap c R θ with hz_def
      have hzR : ‖z - c‖ = R :=
        mem_sphere_iff_norm.mp (circleMap_mem_sphere c hR.le θ)
      rw [norm_smul]
      have hQ : ‖2 * (z - c) / (z - c - (w - c)) ^ 2‖
          ≤ 2 * R / (R - r) ^ 2 := by
        rw [norm_div, norm_mul, norm_pow, hzR]
        have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
        rw [h2]
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact pow_le_pow_left₀ hRr.le (hden θ w hw) 2
      calc ‖φ z‖ * ‖2 * (z - c) / (z - c - (w - c)) ^ 2‖
          ≤ M * (2 * R / (R - r) ^ 2) :=
            mul_le_mul (hM z (circleMap_mem_sphere c hR.le θ)) hQ
              (norm_nonneg _) hM0))
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall (by
      intro θ _ w hw
      exact (hasDerivAt_herglotzRieszKernel_pole
        (hden_ne θ w hw)).const_smul (φ (circleMap c R θ))))
  have hrepr : herglotzTransform φ c R = fun w => (2 * π)⁻¹ •
      ∫ θ in (0:ℝ)..2 * π,
        φ (circleMap c R θ) • herglotzRieszKernel c w (circleMap c R θ) := by
    funext w
    rw [herglotzTransform, Real.circleAverage_def]
  rw [hrepr]
  exact (key.2.const_smul ((2 * π)⁻¹ : ℝ)).differentiableAt

/-! ### W3a: the Poisson operator is the real part, hence harmonic -/

/--
**W3a, identification half.**  On the open disc, the Poisson operator is
the real part of the Herglotz transform.
-/
theorem poissonOperator_eq_re_herglotzTransform {φ : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hφ : ContinuousOn φ (sphere c R)) {w : ℂ}
    (hw : w ∈ ball c R) :
    poissonOperator φ c R w = (herglotzTransform φ c R w).re := by
  have hint : CircleIntegrable (fun z => φ z • herglotzRieszKernel c w z) c R :=
    ContinuousOn.circleIntegrable hR.le
      (hφ.smul (continuousOn_herglotzRieszKernel_sphere hw))
  have hcomm := Complex.reCLM.circleAverage_comp_comm hint
  have hfun : (⇑Complex.reCLM ∘ fun z => φ z • herglotzRieszKernel c w z)
      = fun z => poissonKernel c w z • φ z := by
    funext z
    have hre : poissonKernel c w z = (herglotzRieszKernel c w z).re :=
      congrFun poissonKernel_eq_re_herglotzRieszKernel z
    simp only [Function.comp_apply, Complex.reCLM_apply, Complex.smul_re,
      smul_eq_mul, hre]
    ring
  rw [poissonOperator, herglotzTransform, ← Complex.reCLM_apply, ← hcomm, hfun]

/--
**W3a (pricing row, main statement).**  For boundary data `φ` continuous
on the integration circle, the Poisson operator is harmonic on the open
disc.  Consumed by W4b (jc11's increasing-limit Harnack corollary) and by
the W5 Perron-modification closure.
-/
theorem poissonOperator_harmonicOnNhd {φ : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hφ : ContinuousOn φ (sphere c R)) :
    HarmonicOnNhd (poissonOperator φ c R) (ball c R) := by
  intro w hw
  have han : AnalyticAt ℂ (herglotzTransform φ c R) w :=
    (differentiableOn_herglotzTransform hR hφ).analyticOnNhd isOpen_ball w hw
  have hre : HarmonicAt (fun z => (herglotzTransform φ c R z).re) w :=
    AnalyticAt.harmonicAt_re han
  have heq : (fun z => (herglotzTransform φ c R z).re)
      =ᶠ[𝓝 w] poissonOperator φ c R := by
    filter_upwards [isOpen_ball.mem_nhds hw] with w' hw'
    exact (poissonOperator_eq_re_herglotzTransform hR hφ hw').symm
  exact (harmonicAt_congr_nhds heq).mp hre

/-! ### W3b: normalization -/

/--
**W3b.**  The Poisson operator reproduces constants: instantiation of
Mathlib's Poisson representation formula at a constant function.
-/
theorem poissonOperator_const {c : ℂ} {R : ℝ} (a : ℝ) {w : ℂ}
    (hw : w ∈ ball c R) :
    poissonOperator (fun _ => a) c R w = a := by
  have h := HarmonicContOnCl.circleAverage_poissonKernel_smul
    (f := fun _ : ℂ => a) harmonicContOnCl_const hw
  calc poissonOperator (fun _ => a) c R w
      = Real.circleAverage (poissonKernel c w • fun _ : ℂ => a) c R := rfl
    _ = a := h

/--
**W3b (pricing-row name).**  Kernel normalization: the Poisson operator
sends the constant `1` to `1` on the open disc.
-/
theorem poissonOperator_const_one {c : ℂ} {R : ℝ} {w : ℂ}
    (hw : w ∈ ball c R) :
    poissonOperator (fun _ => 1) c R w = 1 :=
  poissonOperator_const 1 hw

/-! ### W3c: positivity and monotonicity -/

/--
For a pole in the open ball, the Poisson kernel is continuous in the
circle variable on the circle — the real part of the Herglotz–Riesz
kernel, whose denominator does not vanish there.
-/
theorem continuousOn_poissonKernel_sphere {c w : ℂ} {R : ℝ}
    (hw : w ∈ ball c R) :
    ContinuousOn (poissonKernel c w) (sphere c R) := by
  rw [poissonKernel_eq_re_herglotzRieszKernel]
  exact Complex.continuous_re.comp_continuousOn
    (continuousOn_herglotzRieszKernel_sphere hw)

/--
**W3c, kernel positivity.**  On the integration circle the Poisson
kernel of a pole in the open ball is nonnegative — from jc11's lower
kernel estimate (`le_poissonKernel_of_mem_sphere`, W4a).
-/
theorem poissonKernel_nonneg_of_mem_sphere {c w z : ℂ} {R : ℝ}
    (hz : z ∈ sphere c R) (hw : w ∈ ball c R) :
    0 ≤ poissonKernel c w z := by
  have hlow := le_poissonKernel_of_mem_sphere hz hw
  have hwR : ‖w - c‖ < R := mem_ball_iff_norm.mp hw
  have hfrac : 0 ≤ (R - ‖w - c‖) / (R + ‖w - c‖) := by
    have h0R : 0 < R := lt_of_le_of_lt (norm_nonneg _) hwR
    have hnum : 0 ≤ R - ‖w - c‖ := by linarith
    have hden : 0 < R + ‖w - c‖ := by positivity
    exact div_nonneg hnum hden.le
  linarith

/--
**W3c, monotonicity.**  The Poisson operator is monotone in the boundary
datum: pointwise comparison on the circle propagates to the open disc.
-/
theorem poissonOperator_mono {φ ψ : ℂ → ℝ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hφ : ContinuousOn φ (sphere c R)) (hψ : ContinuousOn ψ (sphere c R))
    (hle : ∀ z ∈ sphere c R, φ z ≤ ψ z) {w : ℂ} (hw : w ∈ ball c R) :
    poissonOperator φ c R w ≤ poissonOperator ψ c R w := by
  have hker : ContinuousOn (poissonKernel c w) (sphere c R) :=
    continuousOn_poissonKernel_sphere hw
  have h₁ : CircleIntegrable (fun z => poissonKernel c w z • φ z) c R :=
    ContinuousOn.circleIntegrable hR.le (hker.smul hφ)
  have h₂ : CircleIntegrable (fun z => poissonKernel c w z • ψ z) c R :=
    ContinuousOn.circleIntegrable hR.le (hker.smul hψ)
  apply Real.circleAverage_mono h₁ h₂
  intro z hz
  rw [abs_of_pos hR] at hz
  simp only [smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (hle z hz)
    (poissonKernel_nonneg_of_mem_sphere hz hw)

/--
**W3c, upper bracket.**  A circle-wide upper bound on the boundary datum
bounds the Poisson operator on the open disc: monotonicity against the
constant plus normalization.
-/
theorem poissonOperator_le_of_le {φ : ℂ → ℝ} {c : ℂ} {R M : ℝ}
    (hR : 0 < R) (hφ : ContinuousOn φ (sphere c R))
    (hM : ∀ z ∈ sphere c R, φ z ≤ M) {w : ℂ} (hw : w ∈ ball c R) :
    poissonOperator φ c R w ≤ M := by
  have h := poissonOperator_mono hR hφ continuousOn_const hM hw
  rwa [poissonOperator_const M hw] at h

/--
**W3c, lower bracket.**  Mirror of `poissonOperator_le_of_le`: a
circle-wide lower bound on the boundary datum bounds the Poisson
operator from below on the open disc.  Positivity of the operator for
nonnegative data is the `m := 0` instance.
-/
theorem le_poissonOperator_of_le {φ : ℂ → ℝ} {c : ℂ} {R m : ℝ}
    (hR : 0 < R) (hφ : ContinuousOn φ (sphere c R))
    (hm : ∀ z ∈ sphere c R, m ≤ φ z) {w : ℂ} (hw : w ∈ ball c R) :
    m ≤ poissonOperator φ c R w := by
  have h := poissonOperator_mono hR continuousOn_const hφ hm hw
  rwa [poissonOperator_const m hw] at h

end JacobianChallenge.HolomorphicForms
