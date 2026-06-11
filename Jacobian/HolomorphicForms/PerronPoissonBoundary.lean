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

open Complex InnerProductSpace Metric Real Filter
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

/-! ### W3d M2: the oscillation split -/

/--
The Poisson operator drops constants: subtracting `a` from the boundary
datum subtracts `a` from the operator — `circleAverage_sub` plus the
W3b normalization `poissonOperator_const`.
-/
private lemma poissonOperator_sub_const {φ : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hφ : ContinuousOn φ (sphere c R)) (a : ℝ) {w : ℂ}
    (hw : w ∈ ball c R) :
    poissonOperator (fun z => φ z - a) c R w = poissonOperator φ c R w - a := by
  have hker : ContinuousOn (poissonKernel c w) (sphere c R) :=
    continuousOn_poissonKernel_sphere hw
  have h₁ : CircleIntegrable (fun z => poissonKernel c w z • φ z) c R :=
    ContinuousOn.circleIntegrable hR.le (hker.smul hφ)
  have h₂ : CircleIntegrable (fun z => poissonKernel c w z • a) c R :=
    ContinuousOn.circleIntegrable hR.le (hker.smul continuousOn_const)
  have heq : (fun z => poissonKernel c w z • (φ z - a))
      = fun z => poissonKernel c w z • φ z - poissonKernel c w z • a := by
    funext z
    rw [smul_sub]
  calc poissonOperator (fun z => φ z - a) c R w
      = Real.circleAverage
          (fun z => poissonKernel c w z • φ z - poissonKernel c w z • a) c R := by
        rw [poissonOperator, heq]
    _ = Real.circleAverage (fun z => poissonKernel c w z • φ z) c R
        - Real.circleAverage (fun z => poissonKernel c w z • a) c R :=
        Real.circleAverage_fun_sub h₁ h₂
    _ = poissonOperator φ c R w - poissonOperator (fun _ => a) c R w := rfl
    _ = poissonOperator φ c R w - a := by rw [poissonOperator_const a hw]

/--
Jensen-style bound: the Poisson operator of `ψ` is dominated in absolute
value by the Poisson operator of `|ψ|` — Mathlib's
`abs_circleAverage_le_circleAverage_abs` plus kernel nonnegativity to
pull the absolute value inside the kernel smul.
-/
private lemma abs_poissonOperator_le {ψ : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) {w : ℂ} (hw : w ∈ ball c R) :
    |poissonOperator ψ c R w| ≤ poissonOperator (fun z => |ψ z|) c R w := by
  have habs : |Real.circleAverage (fun z => poissonKernel c w z • ψ z) c R|
      ≤ Real.circleAverage |fun z => poissonKernel c w z • ψ z| c R :=
    Real.abs_circleAverage_le_circleAverage_abs
  have hcongr : Real.circleAverage |fun z => poissonKernel c w z • ψ z| c R
      = Real.circleAverage (fun z => poissonKernel c w z • |ψ z|) c R := by
    apply Real.circleAverage_congr_sphere
    intro z hz
    rw [abs_of_pos hR] at hz
    have hknn : 0 ≤ poissonKernel c w z :=
      poissonKernel_nonneg_of_mem_sphere hz hw
    simp only [Pi.abs_apply, smul_eq_mul, abs_mul, abs_of_nonneg hknn]
  calc |poissonOperator ψ c R w|
      ≤ Real.circleAverage |fun z => poissonKernel c w z • ψ z| c R := habs
    _ = poissonOperator (fun z => |ψ z|) c R w := hcongr

/--
**W3d M2, oscillation split.**  Quantitative boundary estimate for the
Poisson operator: if the boundary datum oscillates by at most `η` around
`φ ζ` on the near arc (`dist z ζ < δ`), is bounded by `M` on the whole
circle, and the kernel of the pole `w` is bounded by `κ` on the far arc
(`δ ≤ dist z ζ`), then `|P[φ](w) - φ ζ| ≤ η + 2Mκ`.

The split is pointwise on the integrand (no indicators): on the near
arc the kernel weight multiplies the oscillation, on the far arc the
kernel bound multiplies the sup bound; the kernel-weighted constant
integrates to `η` by the W3b normalization.  M3 instantiates `η`, `δ`
from continuity of `φ` at `ζ`, `M` from sphere compactness, and `κ`
from the far-arc decay `tendstoUniformlyOn_poissonKernel_far` (M1).
-/
theorem abs_poissonOperator_sub_le {φ : ℂ → ℝ} {c ζ w : ℂ}
    {R δ η M κ : ℝ} (hR : 0 < R) (hφ : ContinuousOn φ (sphere c R))
    (hζ : ζ ∈ sphere c R) (hw : w ∈ ball c R)
    (hM : ∀ z ∈ sphere c R, |φ z| ≤ M) (hη : 0 ≤ η) (hκ : 0 ≤ κ)
    (hnear : ∀ z ∈ sphere c R, dist z ζ < δ → |φ z - φ ζ| ≤ η)
    (hfar : ∀ z ∈ sphere c R, δ ≤ dist z ζ → poissonKernel c w z ≤ κ) :
    |poissonOperator φ c R w - φ ζ| ≤ η + 2 * M * κ := by
  have hker : ContinuousOn (poissonKernel c w) (sphere c R) :=
    continuousOn_poissonKernel_sphere hw
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM ζ hζ)
  have h2Mκ : 0 ≤ 2 * M * κ := by positivity
  -- reduce to the Poisson operator of the absolute oscillation
  rw [← poissonOperator_sub_const hR hφ (φ ζ) hw]
  refine le_trans (abs_poissonOperator_le hR hw) ?_
  -- integrability of both sides of the pointwise majorant
  have hφζ : ContinuousOn (fun z => |φ z - φ ζ|) (sphere c R) :=
    (hφ.sub continuousOn_const).abs
  have h₁ : CircleIntegrable (fun z => poissonKernel c w z • |φ z - φ ζ|) c R :=
    ContinuousOn.circleIntegrable hR.le (hker.smul hφζ)
  have hηint : CircleIntegrable (fun z => poissonKernel c w z • η) c R :=
    ContinuousOn.circleIntegrable hR.le (hker.smul continuousOn_const)
  have h₂ : CircleIntegrable
      (fun z => poissonKernel c w z • η + 2 * M * κ) c R :=
    ContinuousOn.circleIntegrable hR.le
      ((hker.smul continuousOn_const).add continuousOn_const)
  -- the pointwise near/far majorant
  have hpt : ∀ z ∈ sphere c |R|, poissonKernel c w z • |φ z - φ ζ|
      ≤ poissonKernel c w z • η + 2 * M * κ := by
    intro z hz
    rw [abs_of_pos hR] at hz
    have hknn : 0 ≤ poissonKernel c w z :=
      poissonKernel_nonneg_of_mem_sphere hz hw
    simp only [smul_eq_mul]
    rcases lt_or_ge (dist z ζ) δ with hzd | hzd
    · -- near arc: the oscillation bound rides the kernel weight
      have hosc := hnear z hz hzd
      linarith [mul_le_mul_of_nonneg_left hosc hknn]
    · -- far arc: the kernel bound rides the sup bound
      have hKκ := hfar z hz hzd
      have hosc : |φ z - φ ζ| ≤ 2 * M := by
        have h1 := abs_le.mp (hM z hz)
        have h2 := abs_le.mp (hM ζ hζ)
        exact abs_le.mpr ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
      linarith [mul_le_mul hKκ hosc (abs_nonneg _) hκ, mul_nonneg hknn hη]
  -- average the majorant: η by W3b normalization, the constant by itself
  have hηavg : Real.circleAverage (fun z => poissonKernel c w z • η) c R = η :=
    poissonOperator_const η hw
  calc poissonOperator (fun z => |φ z - φ ζ|) c R w
      ≤ Real.circleAverage (fun z => poissonKernel c w z • η + 2 * M * κ) c R :=
        Real.circleAverage_mono h₁ h₂ hpt
    _ = Real.circleAverage (fun z => poissonKernel c w z • η) c R
        + Real.circleAverage (fun _ => 2 * M * κ) c R :=
        Real.circleAverage_fun_add hηint
          (ContinuousOn.circleIntegrable hR.le continuousOn_const)
    _ = η + 2 * M * κ := by
        rw [hηavg, Real.circleAverage_const]

/-! ### W3d M3: the boundary-limit theorem -/

/--
**W3d (main statement), Schwarz boundary limit.**  For boundary data
`φ` continuous on the integration circle, the Poisson operator attains
`φ` at every boundary point: `poissonOperator φ c R w → φ ζ` as
`w → ζ` from inside the disc.

Assembly of M1 + M2: `M` from sphere compactness, the near-arc
oscillation `δ` from continuity of `φ` at `ζ` within the sphere,
`κ := ε / (4M + 2)` from the far-arc kernel decay
`tendstoUniformlyOn_poissonKernel_far`, all fed into the oscillation
split `abs_poissonOperator_sub_le`.  Kept in the neutral `Tendsto` form
per the W3d scope ruling; consumption-shaped corollaries for W5b/W6 are
brokered separately.
-/
theorem poissonOperator_tendsto_of_continuousOn {φ : ℂ → ℝ} {c ζ : ℂ}
    {R : ℝ} (hR : 0 < R) (hφ : ContinuousOn φ (sphere c R))
    (hζ : ζ ∈ sphere c R) :
    Tendsto (poissonOperator φ c R) (𝓝[ball c R] ζ) (𝓝 (φ ζ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- circle-wide sup bound from compactness
  obtain ⟨M, hM⟩ := (isCompact_sphere c R).exists_bound_of_continuousOn hφ
  have hM' : ∀ z ∈ sphere c R, |φ z| ≤ M := by
    intro z hz
    simpa [Real.norm_eq_abs] using hM z hz
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM' ζ hζ)
  -- near-arc oscillation from continuity at ζ within the sphere
  obtain ⟨δ, hδ, hnear⟩ :=
    Metric.continuousWithinAt_iff.mp (hφ ζ hζ) (ε / 2) (by positivity)
  have hnear' : ∀ z ∈ sphere c R, dist z ζ < δ → |φ z - φ ζ| ≤ ε / 2 := by
    intro z hz hzd
    have h := hnear hz hzd
    rw [Real.dist_eq] at h
    exact h.le
  -- far-arc kernel bound, eventually in the pole: M1 at κ
  set κ : ℝ := ε / (4 * M + 2) with hκ_def
  have h42 : (0 : ℝ) < 4 * M + 2 := by linarith
  have hκ : 0 < κ := div_pos hε h42
  have hfar_ev := Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_poissonKernel_far hζ hδ) κ hκ
  filter_upwards [hfar_ev, eventually_mem_nhdsWithin] with w hfar_w hw_ball
  have hfar' : ∀ z ∈ sphere c R, δ ≤ dist z ζ → poissonKernel c w z ≤ κ := by
    intro z hz hzd
    have h := hfar_w z ⟨hz, hzd⟩
    rw [Pi.zero_apply, dist_zero_left, Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h.le
  -- the oscillation split closes the estimate
  have hest := abs_poissonOperator_sub_le hR hφ hζ hw_ball hM'
    (by positivity : (0 : ℝ) ≤ ε / 2) hκ.le hnear' hfar'
  have hgap : 2 * M * κ < ε / 2 := by
    rw [hκ_def, ← mul_div_assoc,
      div_lt_div_iff₀ h42 (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  rw [Real.dist_eq]
  calc |poissonOperator φ c R w - φ ζ| ≤ ε / 2 + 2 * M * κ := hest
    _ < ε := by linarith

/-! ### W3d M4: closed-ball Dirichlet packaging -/

open scoped Classical in
/--
The solution of the disc Dirichlet problem with boundary datum `φ`: the
Poisson extension inside the open disc, the boundary datum itself
outside.  For `φ` continuous on the circle this is continuous on the
closed disc (`continuousOn_poissonSolution`) and harmonic on the open
disc (`poissonSolution_harmonicOnNhd`) — the shape the W7 Perron
envelope and the brokered W5b/W6 corollaries consume.
-/
noncomputable def poissonSolution (φ : ℂ → ℝ) (c : ℂ) (R : ℝ) : ℂ → ℝ :=
  fun z => if z ∈ ball c R then poissonOperator φ c R z else φ z

/--
Inside the open disc, `poissonSolution` is the Poisson operator.
-/
theorem poissonSolution_apply_of_mem_ball {φ : ℂ → ℝ} {c : ℂ} {R : ℝ}
    {z : ℂ} (hz : z ∈ ball c R) :
    poissonSolution φ c R z = poissonOperator φ c R z := by
  simp only [poissonSolution]
  exact if_pos hz

/--
On the boundary circle, `poissonSolution` is the boundary datum.
-/
theorem poissonSolution_apply_of_mem_sphere {φ : ℂ → ℝ} {c : ℂ} {R : ℝ}
    {z : ℂ} (hz : z ∈ sphere c R) :
    poissonSolution φ c R z = φ z := by
  simp only [poissonSolution]
  exact if_neg (Set.disjoint_left.mp sphere_disjoint_ball hz)

/--
**W3d M4, interior half.**  The Dirichlet solution is harmonic on the
open disc: it agrees with the Poisson operator on a neighborhood of
every interior point, so the landed W3a harmonicity transports over.
-/
theorem poissonSolution_harmonicOnNhd {φ : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hφ : ContinuousOn φ (sphere c R)) :
    HarmonicOnNhd (poissonSolution φ c R) (ball c R) := by
  intro w hw
  have heq : poissonOperator φ c R =ᶠ[𝓝 w] poissonSolution φ c R := by
    filter_upwards [isOpen_ball.mem_nhds hw] with w' hw'
    exact (poissonSolution_apply_of_mem_ball hw').symm
  exact (harmonicAt_congr_nhds heq).mp (poissonOperator_harmonicOnNhd hR hφ w hw)

/--
**W3d M4, boundary half (the gluing).**  The Dirichlet solution is
continuous on the closed disc.  At interior points continuity is the
`ContDiffAt` component of harmonicity; at a boundary point the
closed-ball neighborhood filter splits along
`ball ∪ sphere = closedBall` into the interior approach — handled by
the Schwarz boundary limit (M3) — and the along-the-circle approach —
handled by continuity of the boundary datum.
-/
theorem continuousOn_poissonSolution {φ : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hφ : ContinuousOn φ (sphere c R)) :
    ContinuousOn (poissonSolution φ c R) (closedBall c R) := by
  intro z hz
  rcases (mem_closedBall.mp hz).lt_or_eq with hlt | heq
  · -- interior point: continuity from harmonicity
    have hzb : z ∈ ball c R := mem_ball.mpr hlt
    exact ((poissonSolution_harmonicOnNhd hR hφ z hzb).1.continuousAt
      ).continuousWithinAt
  · -- boundary point: glue M3 with continuity of φ along the circle
    have hzs : z ∈ sphere c R := mem_sphere.mpr heq
    show Tendsto (poissonSolution φ c R) (𝓝[closedBall c R] z)
      (𝓝 (poissonSolution φ c R z))
    rw [poissonSolution_apply_of_mem_sphere hzs, ← ball_union_sphere,
      nhdsWithin_union]
    refine Tendsto.sup ?_ ?_
    · -- interior approach: the Schwarz boundary limit
      refine Tendsto.congr' ?_ (poissonOperator_tendsto_of_continuousOn hR hφ hzs)
      filter_upwards [eventually_mem_nhdsWithin] with w hw
      exact (poissonSolution_apply_of_mem_ball hw).symm
    · -- along-the-circle approach: continuity of the boundary datum
      refine Tendsto.congr' ?_ (hφ z hzs)
      filter_upwards [eventually_mem_nhdsWithin] with w hw
      exact (poissonSolution_apply_of_mem_sphere hw).symm

end JacobianChallenge.HolomorphicForms
