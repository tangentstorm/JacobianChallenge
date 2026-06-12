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

/-!
## Harnack convergence, uniform-limit half (W4b-i)

An increasing sequence of harmonic functions on a neighborhood of
`closedBall c R` that is bounded at the center converges pointwise on
the open ball and uniformly on every strictly smaller closed disc.  The
engine is the Harnack upper bound applied to the differences
`h n - h m ≥ 0`: their oscillation on `closedBall c ρ` is controlled by
the single constant `(R + ρ) / (R - ρ)` times their value at the
center, which is Cauchy by monotone boundedness.  Harmonicity of the
limit is the separate W4b-ii step (it consumes the Poisson operator,
W3a).
-/

open Filter Topology

/--
**Harnack upper bound with a `ρ`-uniform constant.**  For `h` harmonic
on a neighborhood of `closedBall c R` and nonnegative on the boundary
circle, the Harnack constant can be taken uniformly over the inner
closed disc: `h w ≤ ((R + ρ) / (R - ρ)) · h c` for all
`w ∈ closedBall c ρ`, `ρ < R`.
-/
theorem harnack_upper_on_closedBall {h : ℂ → ℝ} {c : ℂ} {R ρ : ℝ}
    (hh : HarmonicOnNhd h (closedBall c R))
    (hpos : ∀ z ∈ sphere c R, 0 ≤ h z) (hρ : ρ < R)
    {w : ℂ} (hw : w ∈ closedBall c ρ) :
    h w ≤ ((R + ρ) / (R - ρ)) * h c := by
  have hr : ‖w - c‖ ≤ ρ := mem_closedBall_iff_norm.mp hw
  have hρ0 : 0 ≤ ρ := le_trans (norm_nonneg _) hr
  have hR : 0 < R := lt_of_le_of_lt hρ0 hρ
  have hwball : w ∈ ball c R := mem_ball_iff_norm.mpr (lt_of_le_of_lt hr hρ)
  have habs : |R| = R := abs_of_pos hR
  have hh' : HarmonicOnNhd h (closedBall c |R|) := by rwa [habs]
  have hc0 : 0 ≤ h c := by
    rw [← HarmonicOnNhd.circleAverage_eq hh']
    apply circleAverage_nonneg_of_nonneg
    rwa [habs]
  have hconst : (R + ‖w - c‖) / (R - ‖w - c‖) ≤ (R + ρ) / (R - ρ) := by
    have h₂ : 0 < R - ‖w - c‖ := by linarith [lt_of_le_of_lt hr hρ]
    have h₃ : 0 < R - ρ := by linarith
    rw [div_le_div_iff₀ h₂ h₃]
    nlinarith [norm_nonneg (w - c)]
  calc h w
      ≤ (R + ‖w - c‖) / (R - ‖w - c‖) * h c := harnack_upper hh hwball hpos
    _ ≤ (R + ρ) / (R - ρ) * h c := mul_le_mul_of_nonneg_right hconst hc0

/--
**Harnack convergence, uniform-limit half** (W4b-i; pricing doc §3.1,
row W4 corollary): an increasing sequence of harmonic functions on a
neighborhood of `closedBall c R` that is bounded at the center
converges pointwise on the open ball, uniformly on every closed disc
`closedBall c ρ` with `ρ < R`.  Harmonicity of the limit is W4b-ii.
-/
theorem harnack_increasing_tendstoUniformlyOn {h : ℕ → ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hh : ∀ n, HarmonicOnNhd (h n) (closedBall c R))
    (hmono : ∀ z ∈ closedBall c R, Monotone fun n => h n z)
    (hbdd : BddAbove (Set.range fun n => h n c)) :
    ∃ H : ℂ → ℝ,
      (∀ z ∈ ball c R, Tendsto (fun n => h n z) atTop (𝓝 (H z))) ∧
      ∀ ρ, ρ < R → TendstoUniformlyOn (fun n z => h n z) H atTop (closedBall c ρ) := by
  have hsub : ∀ m n : ℕ, HarmonicOnNhd (h n - h m) (closedBall c R) :=
    fun m n => (hh n).sub (hh m)
  have hsubpos : ∀ m n : ℕ, m ≤ n → ∀ z ∈ sphere c R, 0 ≤ (h n - h m) z := by
    intro m n hmn z hz
    simp only [Pi.sub_apply, sub_nonneg]
    exact hmono z (sphere_subset_closedBall hz) hmn
  -- pointwise boundedness on the open ball, via Harnack on `h n - h 0`
  have hptbdd : ∀ z ∈ ball c R, BddAbove (Set.range fun n => h n z) := by
    intro z hz
    obtain ⟨M, hM⟩ := hbdd
    have hzR : ‖z - c‖ < R := mem_ball_iff_norm.mp hz
    have hR : 0 < R := pos_of_mem_ball hz
    have hCpos : 0 ≤ (R + ‖z - c‖) / (R - ‖z - c‖) :=
      div_nonneg (by linarith [norm_nonneg (z - c)]) (by linarith)
    refine ⟨h 0 z + (R + ‖z - c‖) / (R - ‖z - c‖) * (M - h 0 c), ?_⟩
    rintro x ⟨n, rfl⟩
    have hd := harnack_upper (hsub 0 n) hz (hsubpos 0 n (Nat.zero_le n))
    simp only [Pi.sub_apply] at hd
    have hMc : h n c - h 0 c ≤ M - h 0 c := by
      have := hM (Set.mem_range_self n)
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hMc hCpos]
  have hptlim : ∀ z ∈ ball c R,
      Tendsto (fun n => h n z) atTop (𝓝 (⨆ n, h n z)) :=
    fun z hz => tendsto_atTop_ciSup (hmono z (ball_subset_closedBall hz)) (hptbdd z hz)
  refine ⟨fun z => ⨆ n, h n z, hptlim, ?_⟩
  intro ρ hρ
  rcases lt_or_ge ρ 0 with hneg | hρ0
  · rw [closedBall_eq_empty.mpr hneg]
    exact tendstoUniformlyOn_empty
  have hR : 0 < R := lt_of_le_of_lt hρ0 hρ
  have hcball : c ∈ ball c R := mem_ball_self hR
  have hCpos : 0 < (R + ρ) / (R - ρ) := div_pos (by linarith) (by linarith)
  -- the limit inherits the difference bound, uniformly over the inner disc
  have hlimbd : ∀ n : ℕ, ∀ w ∈ closedBall c ρ,
      (⨆ k, h k w) - h n w ≤ (R + ρ) / (R - ρ) * ((⨆ k, h k c) - h n c) := by
    intro n w hw
    have hwball : w ∈ ball c R :=
      mem_ball_iff_norm.mpr (lt_of_le_of_lt (mem_closedBall_iff_norm.mp hw) hρ)
    have hf : Tendsto (fun k => h k w - h n w) atTop (𝓝 ((⨆ k, h k w) - h n w)) :=
      (hptlim w hwball).sub tendsto_const_nhds
    have hg : Tendsto (fun k => (R + ρ) / (R - ρ) * (h k c - h n c)) atTop
        (𝓝 ((R + ρ) / (R - ρ) * ((⨆ k, h k c) - h n c))) :=
      ((hptlim c hcball).sub tendsto_const_nhds).const_mul _
    apply le_of_tendsto_of_tendsto hf hg
    filter_upwards [eventually_ge_atTop n] with k hk
    have := harnack_upper_on_closedBall (hsub n k) (hsubpos n k hk) hρ hw
    simpa [Pi.sub_apply] using this
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hev : ∀ᶠ n in atTop, (⨆ k, h k c) - h n c < ε / ((R + ρ) / (R - ρ)) := by
    have hlim0 : Tendsto (fun n => (⨆ k, h k c) - h n c) atTop (𝓝 0) := by
      simpa using Filter.Tendsto.const_sub (⨆ k, h k c) (hptlim c hcball)
    exact hlim0.eventually_lt_const (by positivity)
  filter_upwards [hev] with n hn w hw
  have hwball : w ∈ ball c R :=
    mem_ball_iff_norm.mpr (lt_of_le_of_lt (mem_closedBall_iff_norm.mp hw) hρ)
  have hub := hlimbd n w hw
  have hnn : h n w ≤ ⨆ k, h k w := le_ciSup (hptbdd w hwball) n
  rw [Real.dist_eq, abs_of_nonneg (by linarith : (0:ℝ) ≤ (⨆ k, h k w) - h n w)]
  calc (⨆ k, h k w) - h n w
      ≤ (R + ρ) / (R - ρ) * ((⨆ k, h k c) - h n c) := hub
    _ < (R + ρ) / (R - ρ) * (ε / ((R + ρ) / (R - ρ))) :=
        mul_lt_mul_of_pos_left hn hCpos
    _ = ε := by rw [mul_comm]; exact div_mul_cancel₀ ε hCpos.ne'

/-!
## Strong maximum principle on balls (W7-iii)

The classical Harnack ⇒ strong-max argument: for `g ≤ 0` harmonic on a
ball with an interior zero, the Harnack upper bound applied to `-g ≥ 0`
on sub-discs shows the zero set is open; it is relatively closed by
continuity, and the ball is preconnected, so the zero set is
everything.  This is the interior-rigidity input for the Perron
envelope's second-comparison step (W7-ii); it is NOT the weak maximum
principle (`WeakMaxPrincipleInput`, jc3's W1) — boundary bounds cannot
see a touching point.
-/

/--
Local propagation of an interior zero: if `g ≤ 0` is harmonic on
`ball c R` and vanishes at `z₀`, it vanishes on the ball of radius
`(R - ‖z₀ - c‖) / 2` about `z₀`.  Harnack's upper bound for `-g ≥ 0`
on the sub-disc is `(-g) w ≤ C(w) · (-g) z₀ = 0`.
-/
private lemma zero_ball_of_zero_center {g : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hg : HarmonicOnNhd g (ball c R))
    (hle : ∀ z ∈ ball c R, g z ≤ 0)
    {z₀ : ℂ} (hz₀ : z₀ ∈ ball c R) (hzero : g z₀ = 0) :
    ∀ w ∈ ball z₀ ((R - ‖z₀ - c‖) / 2), g w = 0 := by
  intro w hw
  set r := (R - ‖z₀ - c‖) / 2 with hrdef
  have hz₀R : ‖z₀ - c‖ < R := mem_ball_iff_norm.mp hz₀
  have hsub : closedBall z₀ r ⊆ ball c R := by
    intro x hx
    rw [mem_ball_iff_norm]
    have hxz : ‖x - z₀‖ ≤ r := mem_closedBall_iff_norm.mp hx
    calc ‖x - c‖ = ‖x - z₀ + (z₀ - c)‖ := by ring_nf
      _ ≤ ‖x - z₀‖ + ‖z₀ - c‖ := norm_add_le _ _
      _ < R := by rw [hrdef] at hxz; linarith
  have hneg : HarmonicOnNhd (-g) (closedBall z₀ r) := (hg.mono hsub).neg
  have hpos : ∀ z ∈ sphere z₀ r, 0 ≤ (-g) z := by
    intro z hz
    have hzball : z ∈ ball c R := hsub (sphere_subset_closedBall hz)
    simp only [Pi.neg_apply]
    linarith [hle z hzball]
  have hub := harnack_upper hneg hw hpos
  have h0 : (-g) z₀ = 0 := by simp [hzero]
  rw [h0, mul_zero] at hub
  have hge : 0 ≤ (-g) w := by
    have hwball : w ∈ ball c R := hsub (ball_subset_closedBall hw)
    simp only [Pi.neg_apply]
    linarith [hle w hwball]
  have : (-g) w = 0 := le_antisymm hub hge
  simpa [neg_eq_zero] using this

/--
**Strong maximum principle on balls** (W7-iii).  A harmonic `g ≤ 0` on
`ball c R` vanishing at one interior point vanishes identically: the
zero set is open by Harnack propagation, the negative set is open by
continuity, and the ball is preconnected.
-/
theorem harnack_strong_max_ball {g : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hg : HarmonicOnNhd g (ball c R))
    (hle : ∀ z ∈ ball c R, g z ≤ 0)
    {x₀ : ℂ} (hx₀ : x₀ ∈ ball c R) (hzero : g x₀ = 0) :
    ∀ z ∈ ball c R, g z = 0 := by
  -- the union of all propagation balls around interior zeros
  set U : Set ℂ := ⋃ (z : ℂ) (_ : z ∈ ball c R ∧ g z = 0),
    ball z ((R - ‖z - c‖) / 2) with hU
  have hUopen : IsOpen U :=
    isOpen_iUnion fun z => isOpen_iUnion fun _ => isOpen_ball
  have hUzero : ∀ w ∈ U ∩ ball c R, g w = 0 := by
    rintro w ⟨hwU, -⟩
    simp only [hU, Set.mem_iUnion] at hwU
    obtain ⟨z, ⟨hz, hz0⟩, hwz⟩ := hwU
    exact zero_ball_of_zero_center hg hle hz hz0 w hwz
  have hmem_self : ∀ z ∈ ball c R, g z = 0 → z ∈ U := by
    intro z hz hz0
    have hzR : ‖z - c‖ < R := mem_ball_iff_norm.mp hz
    simp only [hU, Set.mem_iUnion]
    exact ⟨z, ⟨hz, hz0⟩, mem_ball_self (by linarith)⟩
  -- the strictly-negative locus
  set W : Set ℂ := ball c R ∩ g ⁻¹' (Set.Iio 0) with hW
  have hWopen : IsOpen W :=
    hg.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_Iio
  -- the two open sets cover the ball and are disjoint inside it
  have hcover : ball c R ⊆ U ∪ W := by
    intro z hz
    rcases lt_or_eq_of_le (hle z hz) with hlt | heq
    · exact Or.inr ⟨hz, hlt⟩
    · exact Or.inl (hmem_self z hz heq)
  have hUne : (ball c R ∩ U).Nonempty :=
    ⟨x₀, hx₀, hmem_self x₀ hx₀ hzero⟩
  intro z hz
  by_contra hne0
  have hWne : (ball c R ∩ W).Nonempty :=
    ⟨z, hz, hz, lt_of_le_of_ne (hle z hz) hne0⟩
  obtain ⟨w, hwball, hwU, hwW⟩ :=
    (convex_ball c R).isPreconnected U W hUopen hWopen hcover hUne hWne
  have h0 := hUzero w ⟨hwU, hwball⟩
  have hneg : g w < 0 := hwW.2
  linarith

/--
**Interior-touch rigidity** (the shape W7-ii consumes): two harmonic
functions on a ball with `h₁ ≤ h₂` throughout and equality at one
interior point are equal on the whole ball.
-/
theorem eq_on_ball_of_harmonic_le_of_eq_at {h₁ h₂ : ℂ → ℝ} {c : ℂ}
    {R : ℝ}
    (hh₁ : HarmonicOnNhd h₁ (ball c R)) (hh₂ : HarmonicOnNhd h₂ (ball c R))
    (hle : ∀ z ∈ ball c R, h₁ z ≤ h₂ z)
    {x₀ : ℂ} (hx₀ : x₀ ∈ ball c R) (heq : h₁ x₀ = h₂ x₀) :
    ∀ z ∈ ball c R, h₁ z = h₂ z := by
  have key := harnack_strong_max_ball (hh₁.sub hh₂)
    (fun z hz => by simp only [Pi.sub_apply]; linarith [hle z hz])
    hx₀ (by simp only [Pi.sub_apply]; linarith)
  intro z hz
  have := key z hz
  simp only [Pi.sub_apply] at this
  linarith

end JacobianChallenge.HolomorphicForms



