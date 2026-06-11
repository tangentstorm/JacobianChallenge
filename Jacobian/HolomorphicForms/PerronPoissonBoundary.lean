import Jacobian.HolomorphicForms.PerronPoissonOperator

/-!
# Poisson boundary limit on chart discs (Perron engine B2 toolbox W3d)

Blueprint: `docs/perron-b2-dirichlet-phase0.md` §4, row W3d (revived
2026-06-11, continuous-data scope); tracking #232, node
`lem:stage-dirichlet-harmonic-exists`.

This file develops the boundary half of the disc Dirichlet problem for
the Poisson operator `poissonOperator` of `PerronPoissonOperator.lean`:
the Schwarz boundary-limit theorem for continuous boundary data, via the
classical approximate-identity argument (near-arc/far-arc split).

This commit (M1): the far-arc kernel decay.  As the pole `w` approaches
a boundary point `ζ` from inside the disc, the Poisson kernel
`poissonKernel c w z` dies **uniformly** over the circle points `z`
kept at distance at least `δ` from `ζ`
(`tendstoUniformlyOn_poissonKernel_far`).  The mechanism: the kernel
numerator `R² - ‖w - c‖²` vanishes as `w → ζ` while the denominator
`‖z - w‖²` stays at least `(δ/2)²` once `w` is within `δ/2` of `ζ`.

The oscillation split (M2), the boundary-limit theorem itself (M3), and
the closed-ball Dirichlet packaging (M4) are the follow-up commits.
-/

namespace JacobianChallenge.HolomorphicForms

open Complex Metric Real Filter
open scoped Real Topology

/--
Far-arc denominator separation: if `z` keeps distance `δ` from `ζ` and
`w` is within `δ / 2` of `ζ`, then `z` keeps distance `δ / 2` from `w` —
triangle inequality through `ζ`.
-/
private lemma half_le_dist_of_far {ζ z w : ℂ} {δ : ℝ}
    (hz_far : δ ≤ dist z ζ) (hw_near : dist w ζ ≤ δ / 2) :
    δ / 2 ≤ dist z w := by
  have htri : dist z ζ ≤ dist z w + dist w ζ := dist_triangle z w ζ
  linarith

/--
Numerator decay: as the pole approaches the boundary point `ζ` of the
integration circle, the Poisson kernel numerator `R ^ 2 - ‖w - c‖ ^ 2`
tends to `0`.
-/
private lemma tendsto_kernel_numerator {c ζ : ℂ} {R : ℝ}
    (hζ : ζ ∈ sphere c R) :
    Tendsto (fun w : ℂ => R ^ 2 - ‖w - c‖ ^ 2) (𝓝[ball c R] ζ) (𝓝 0) := by
  have hζR : ‖ζ - c‖ = R := mem_sphere_iff_norm.mp hζ
  have hcont : Tendsto (fun w : ℂ => R ^ 2 - ‖w - c‖ ^ 2) (𝓝 ζ)
      (𝓝 (R ^ 2 - ‖ζ - c‖ ^ 2)) := (Continuous.tendsto (by fun_prop) ζ)
  have h0 : R ^ 2 - ‖ζ - c‖ ^ 2 = 0 := by rw [hζR]; ring
  rw [h0] at hcont
  exact hcont.mono_left nhdsWithin_le_nhds

/--
**W3d M1, far-arc kernel decay.**  As the pole `w` approaches a boundary
point `ζ` of the integration circle from inside the disc, the Poisson
kernel dies uniformly on the part of the circle at distance at least `δ`
from `ζ`.  This is the far-arc half of the approximate-identity argument
for the Schwarz boundary-limit theorem (M3); the `ε`-form consumed by
the oscillation split (M2) is `Metric.tendstoUniformlyOn_iff`.
-/
theorem tendstoUniformlyOn_poissonKernel_far {c ζ : ℂ} {R δ : ℝ}
    (hζ : ζ ∈ sphere c R) (hδ : 0 < δ) :
    TendstoUniformlyOn (fun w z => poissonKernel c w z) 0
      (𝓝[ball c R] ζ) {z ∈ sphere c R | δ ≤ dist z ζ} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- the three eventual facts about the pole `w`
  have hnear : ∀ᶠ w in 𝓝[ball c R] ζ, dist w ζ ≤ δ / 2 := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds
      (closedBall_mem_nhds ζ (by positivity : (0 : ℝ) < δ / 2))] with w hw
    exact mem_closedBall.mp hw
  have hsmall : ∀ᶠ w in 𝓝[ball c R] ζ,
      R ^ 2 - ‖w - c‖ ^ 2 < ε * (δ / 2) ^ 2 :=
    (tendsto_kernel_numerator hζ).eventually_lt_const (by positivity)
  filter_upwards [hnear, hsmall, eventually_mem_nhdsWithin]
    with w hw_near hw_small hw_ball z hz
  obtain ⟨hz_sphere, hz_far⟩ := hz
  have hzR : ‖z - c‖ = R := mem_sphere_iff_norm.mp hz_sphere
  have hknn : 0 ≤ poissonKernel c w z :=
    poissonKernel_nonneg_of_mem_sphere hz_sphere hw_ball
  have hnum_nonneg : 0 ≤ R ^ 2 - ‖w - c‖ ^ 2 := by
    have hwR : ‖w - c‖ < R := mem_ball_iff_norm.mp hw_ball
    nlinarith [norm_nonneg (w - c)]
  -- the kernel in far-arc normal form
  have hkernel : poissonKernel c w z
      = (R ^ 2 - ‖w - c‖ ^ 2) / dist z w ^ 2 := by
    rw [poissonKernel_def, hzR, sub_sub_sub_cancel_right, dist_eq_norm]
  -- denominator separation and the resulting bound
  have hzw : δ / 2 ≤ dist z w := half_le_dist_of_far hz_far hw_near
  have hbound : poissonKernel c w z
      ≤ (R ^ 2 - ‖w - c‖ ^ 2) / (δ / 2) ^ 2 := by
    rw [hkernel]
    gcongr
  have hlt : (R ^ 2 - ‖w - c‖ ^ 2) / (δ / 2) ^ 2 < ε := by
    rw [div_lt_iff₀ (by positivity)]
    linarith
  rw [Pi.zero_apply, dist_zero_left, Real.norm_eq_abs, abs_of_nonneg hknn]
  exact lt_of_le_of_lt hbound hlt

end JacobianChallenge.HolomorphicForms
