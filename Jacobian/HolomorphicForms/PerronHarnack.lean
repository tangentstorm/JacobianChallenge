import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Harnack inequality on discs (Perron engine B2 toolbox W4a)

Blueprint node: `lem:perron-harnack-disc`.

The Perron envelope machinery (phase-0 pricing §3.1, row W4) needs the
two-sided Harnack inequality for nonnegative harmonic functions on
discs: for `h ≥ 0` harmonic on a neighborhood of `closedBall c R` and
`w` in the open ball,

  `((R - r) / (R + r)) · h c  ≤  h w  ≤  ((R + r) / (R - r)) · h c`

with `r = ‖w - c‖`.  Mathlib has no Harnack inequality; it does have the
exact leaves: the Poisson representation of harmonic functions
(`InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul`),
the mean-value property (`HarmonicOnNhd.circleAverage_eq`), and the
two-sided Herglotz–Riesz kernel estimates
(`re_herglotzRieszKernel_le` / `le_re_herglotzRieszKernel`).  Harnack is
the composite: bound the kernel by constants on the integration circle,
multiply by `h ≥ 0`, and compare circle averages.

Outputs: the kernel bounds restated for `poissonKernel` (reusable bridge
leaves), and the lower/upper/two-sided Harnack inequalities.  The core
lemmas only need `h ≥ 0` on the *circle* of integration — strictly
weaker than nonnegativity on the ball, which is what the W4b
increasing-sequence corollary applies to differences `h k - h j`.  Pure
Mathlib-leaf composition — no stage dependencies.
-/

namespace JacobianChallenge.HolomorphicForms

open Complex InnerProductSpace Metric Real

/--
Upper bound for the Poisson kernel on the integration circle: for `z` on
the circle of radius `R` about `c` and `w` in the open ball,
`poissonKernel c w z ≤ (R + ‖w - c‖) / (R - ‖w - c‖)`.  This is
Mathlib's `re_herglotzRieszKernel_le` transported through
`poissonKernel_eq_re_herglotzRieszKernel`.
-/
theorem poissonKernel_le_of_mem_sphere {c w z : ℂ} {R : ℝ}
    (hz : z ∈ sphere c R) (hw : w ∈ ball c R) :
    poissonKernel c w z ≤ (R + ‖w - c‖) / (R - ‖w - c‖) := by
  have hk := re_herglotzRieszKernel_le hz hw
  calc poissonKernel c w z
      = ((z - c + (w - c)) / (z - c - (w - c))).re := by
        rw [poissonKernel_eq_re_herglotzRieszKernel]
        simp [herglotzRieszKernel_def]
    _ ≤ (R + ‖w - c‖) / (R - ‖w - c‖) := hk

/--
Lower bound for the Poisson kernel on the integration circle: for `z` on
the circle of radius `R` about `c` and `w` in the open ball,
`(R - ‖w - c‖) / (R + ‖w - c‖) ≤ poissonKernel c w z`.  This is
Mathlib's `le_re_herglotzRieszKernel` transported through
`poissonKernel_eq_re_herglotzRieszKernel`.
-/
theorem le_poissonKernel_of_mem_sphere {c w z : ℂ} {R : ℝ}
    (hz : z ∈ sphere c R) (hw : w ∈ ball c R) :
    (R - ‖w - c‖) / (R + ‖w - c‖) ≤ poissonKernel c w z := by
  have hk := le_re_herglotzRieszKernel hz hw
  calc (R - ‖w - c‖) / (R + ‖w - c‖)
      ≤ ((z - c + (w - c)) / (z - c - (w - c))).re := hk
    _ = poissonKernel c w z := by
        rw [poissonKernel_eq_re_herglotzRieszKernel]
        simp [herglotzRieszKernel_def]

/--
The Poisson kernel for a pole `w` in the open ball is continuous on the
integration circle: the denominator `‖z - w‖²` cannot vanish there since
`‖w - c‖ < R = ‖z - c‖`.
-/
private lemma continuousOn_poissonKernel_sphere {c w : ℂ} {R : ℝ}
    (hw : w ∈ ball c R) :
    ContinuousOn (poissonKernel c w) (sphere c R) := by
  have hdef : poissonKernel c w
      = fun z => (‖z - c‖ ^ 2 - ‖w - c‖ ^ 2) / ‖z - c - (w - c)‖ ^ 2 := rfl
  rw [hdef]
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro z hz
  have hzR : ‖z - c‖ = R := mem_sphere_iff_norm.mp hz
  have hwR : ‖w - c‖ < R := mem_ball_iff_norm.mp hw
  have hne : z - c - (w - c) ≠ 0 := by
    intro hzero
    rw [← sub_eq_zero.mp hzero] at hwR
    exact absurd hzR (ne_of_lt hwR)
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)

/--
**Harnack inequality on discs, upper half.**  If `h` is harmonic on a
neighborhood of `closedBall c R` and nonnegative on the boundary circle,
then for `w` in the open ball,
`h w ≤ ((R + ‖w - c‖) / (R - ‖w - c‖)) · h c`.
-/
theorem harnack_upper {h : ℂ → ℝ} {c w : ℂ} {R : ℝ}
    (hh : HarmonicOnNhd h (closedBall c R)) (hw : w ∈ ball c R)
    (hpos : ∀ z ∈ sphere c R, 0 ≤ h z) :
    h w ≤ ((R + ‖w - c‖) / (R - ‖w - c‖)) * h c := by
  have hR : 0 < R := pos_of_mem_ball hw
  have habs : |R| = R := abs_of_pos hR
  have hcont : ContinuousOn h (sphere c R) :=
    hh.continuousOn.mono sphere_subset_closedBall
  have hkint : CircleIntegrable (poissonKernel c w • h) c R :=
    ((continuousOn_poissonKernel_sphere hw).smul hcont).circleIntegrable hR.le
  have hsint :
      CircleIntegrable (fun z => ((R + ‖w - c‖) / (R - ‖w - c‖)) • h z) c R :=
    (hcont.const_smul _).circleIntegrable hR.le
  have hh' : HarmonicOnNhd h (closedBall c |R|) := by rwa [habs]
  calc h w
      = Real.circleAverage (poissonKernel c w • h) c R :=
        (hh.circleAverage_poissonKernel_smul hw).symm
    _ ≤ Real.circleAverage
          (fun z => ((R + ‖w - c‖) / (R - ‖w - c‖)) • h z) c R := by
        apply circleAverage_mono hkint hsint
        intro z hz
        rw [habs] at hz
        have := mul_le_mul_of_nonneg_right
          (poissonKernel_le_of_mem_sphere hz hw) (hpos z hz)
        simpa [Pi.smul_apply', smul_eq_mul] using this
    _ = ((R + ‖w - c‖) / (R - ‖w - c‖)) * h c := by
        rw [circleAverage_fun_smul, HarmonicOnNhd.circleAverage_eq hh',
          smul_eq_mul]

/--
**Harnack inequality on discs, lower half.**  If `h` is harmonic on a
neighborhood of `closedBall c R` and nonnegative on the boundary circle,
then for `w` in the open ball,
`((R - ‖w - c‖) / (R + ‖w - c‖)) · h c ≤ h w`.
-/
theorem harnack_lower {h : ℂ → ℝ} {c w : ℂ} {R : ℝ}
    (hh : HarmonicOnNhd h (closedBall c R)) (hw : w ∈ ball c R)
    (hpos : ∀ z ∈ sphere c R, 0 ≤ h z) :
    ((R - ‖w - c‖) / (R + ‖w - c‖)) * h c ≤ h w := by
  have hR : 0 < R := pos_of_mem_ball hw
  have habs : |R| = R := abs_of_pos hR
  have hcont : ContinuousOn h (sphere c R) :=
    hh.continuousOn.mono sphere_subset_closedBall
  have hkint : CircleIntegrable (poissonKernel c w • h) c R :=
    ((continuousOn_poissonKernel_sphere hw).smul hcont).circleIntegrable hR.le
  have hsint :
      CircleIntegrable (fun z => ((R - ‖w - c‖) / (R + ‖w - c‖)) • h z) c R :=
    (hcont.const_smul _).circleIntegrable hR.le
  have hh' : HarmonicOnNhd h (closedBall c |R|) := by rwa [habs]
  calc ((R - ‖w - c‖) / (R + ‖w - c‖)) * h c
      = Real.circleAverage
          (fun z => ((R - ‖w - c‖) / (R + ‖w - c‖)) • h z) c R := by
        rw [circleAverage_fun_smul, HarmonicOnNhd.circleAverage_eq hh',
          smul_eq_mul]
    _ ≤ Real.circleAverage (poissonKernel c w • h) c R := by
        apply circleAverage_mono hsint hkint
        intro z hz
        rw [habs] at hz
        have := mul_le_mul_of_nonneg_right
          (le_poissonKernel_of_mem_sphere hz hw) (hpos z hz)
        simpa [Pi.smul_apply', smul_eq_mul] using this
    _ = h w := hh.circleAverage_poissonKernel_smul hw

/--
**Two-sided Harnack inequality on discs** (pricing doc §3.1, row W4):
for `h ≥ 0` harmonic on a neighborhood of `closedBall c R` and `w` in
the open ball,
`((R - r) / (R + r)) · h c ≤ h w ≤ ((R + r) / (R - r)) · h c` with
`r = ‖w - c‖`.
-/
theorem harnack {h : ℂ → ℝ} {c w : ℂ} {R : ℝ}
    (hh : HarmonicOnNhd h (closedBall c R)) (hw : w ∈ ball c R)
    (hpos : ∀ z ∈ closedBall c R, 0 ≤ h z) :
    ((R - ‖w - c‖) / (R + ‖w - c‖)) * h c ≤ h w ∧
      h w ≤ ((R + ‖w - c‖) / (R - ‖w - c‖)) * h c :=
  have hs : ∀ z ∈ sphere c R, 0 ≤ h z :=
    fun z hz => hpos z (sphere_subset_closedBall hz)
  ⟨harnack_lower hh hw hs, harnack_upper hh hw hs⟩

end JacobianChallenge.HolomorphicForms

