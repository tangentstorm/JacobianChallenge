import Jacobian.HolomorphicForms.PerronPoissonOperator

/-!
# Harnack convergence: the limit is harmonic (Perron engine B2 toolbox W4b-ii)

Blueprint node: `lem:perron-harnack-harmonic-limit`.

This completes the W4 increasing-limit corollary (pricing doc §3.1, row
W4): the locally uniform limit produced by
`harnack_increasing_tendstoUniformlyOn` (W4b-i, `PerronHarnack.lean`) is
harmonic on the open disc.  The route avoids the mean-value converse
(absent from Mathlib): on a strictly smaller disc each `h n` *is* its
Poisson integral (Mathlib's representation theorem), uniform convergence
on the circle passes the identity to the limit, so the limit lands in
`poissonOperator` form — harmonic in the pole by W3a
(`poissonOperator_harmonicOnNhd`, `PerronPoissonOperator.lean`).

This file is separate from `PerronHarnack.lean` because the W3a file
imports `PerronHarnack` (it consumes the W4a kernel estimates), so the
consumer of both must sit above them in the import order.

Outputs: `harmonicOnNhd_ball_of_tendstoUniformlyOn` (uniform-on-inner-
discs limits of harmonic functions are harmonic — no monotonicity
needed), and `harnack_increasing_limit_harmonic` (the full W4 package in
the W7 consumer shape: pointwise + locally uniform + harmonic limit).
-/

namespace JacobianChallenge.HolomorphicForms

open Complex InnerProductSpace Metric Real Filter Topology

/--
The Poisson operator is additive in the boundary datum against
differences: `P[φ - ψ] = P[φ] - P[ψ]` on the open disc, for data
continuous on the circle.
-/
private lemma poissonOperator_sub {φ ψ : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hφ : ContinuousOn φ (sphere c R))
    (hψ : ContinuousOn ψ (sphere c R)) {w : ℂ} (hw : w ∈ ball c R) :
    poissonOperator (φ - ψ) c R w
      = poissonOperator φ c R w - poissonOperator ψ c R w := by
  have hK := continuousOn_poissonKernel_sphere hw
  have hintφ : CircleIntegrable (fun z => poissonKernel c w z • φ z) c R :=
    (hK.smul hφ).circleIntegrable hR.le
  have hintψ : CircleIntegrable (fun z => poissonKernel c w z • ψ z) c R :=
    (hK.smul hψ).circleIntegrable hR.le
  unfold poissonOperator
  simp only [Pi.sub_apply, smul_sub]
  exact circleAverage_fun_sub hintφ hintψ

/--
Continuity of the Poisson operator in the boundary datum: if `h n → H`
uniformly on the circle (all data continuous there), then
`P[h n] w → P[H] w` for every `w` in the open disc.  The estimate is
`|P[h n] w - P[H] w| = |P[h n - H] w| ≤ sup_circle |h n - H|` via the
W3c brackets.
-/
private lemma tendsto_poissonOperator_of_tendstoUniformlyOn {h : ℕ → ℂ → ℝ}
    {H : ℂ → ℝ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hcont : ∀ n, ContinuousOn (h n) (sphere c R))
    (hHcont : ContinuousOn H (sphere c R))
    (hunif : TendstoUniformlyOn (fun n z => h n z) H atTop (sphere c R))
    {w : ℂ} (hw : w ∈ ball c R) :
    Tendsto (fun n => poissonOperator (h n) c R w) atTop
      (𝓝 (poissonOperator H c R w)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hunif (ε / 2) (by linarith)]
    with n hn
  have hsub_cont : ContinuousOn (h n - H) (sphere c R) := (hcont n).sub hHcont
  have hup : ∀ z ∈ sphere c R, (h n - H) z ≤ ε / 2 := by
    intro z hz
    have := abs_lt.mp ((Real.dist_eq _ _) ▸ hn z hz)
    simp only [Pi.sub_apply]
    linarith [this.1, this.2]
  have hlo : ∀ z ∈ sphere c R, -(ε / 2) ≤ (h n - H) z := by
    intro z hz
    have := abs_lt.mp ((Real.dist_eq _ _) ▸ hn z hz)
    simp only [Pi.sub_apply]
    linarith [this.1, this.2]
  have hkey : |poissonOperator (h n) c R w - poissonOperator H c R w| ≤ ε / 2 := by
    rw [← poissonOperator_sub hR (hcont n) hHcont hw, abs_le]
    exact ⟨le_poissonOperator_of_le hR hsub_cont hlo hw,
      poissonOperator_le_of_le hR hsub_cont hup hw⟩
  rw [Real.dist_eq]
  calc |poissonOperator (h n) c R w - poissonOperator H c R w|
      ≤ ε / 2 := hkey
    _ < ε := by linarith

/--
**Harmonic limit theorem on discs.**  If a sequence of functions
harmonic on a neighborhood of `closedBall c R` converges to `H`
uniformly on every closed disc `closedBall c ρ` with `ρ < R`, then `H`
is harmonic on the open ball.  No monotonicity is required.  Each `h n`
is its Poisson integral on a strictly smaller disc; the identity passes
to the limit and exhibits `H` in `poissonOperator` form, which is
harmonic in the pole (W3a).
-/
theorem harmonicOnNhd_ball_of_tendstoUniformlyOn {h : ℕ → ℂ → ℝ} {H : ℂ → ℝ}
    {c : ℂ} {R : ℝ}
    (hh : ∀ n, HarmonicOnNhd (h n) (closedBall c R))
    (hunif : ∀ ρ, ρ < R →
      TendstoUniformlyOn (fun n z => h n z) H atTop (closedBall c ρ)) :
    HarmonicOnNhd H (ball c R) := by
  intro w₀ hw₀
  have hw₀R : ‖w₀ - c‖ < R := mem_ball_iff_norm.mp hw₀
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg _) hw₀R
  set ρ := (‖w₀ - c‖ + R) / 2 with hρdef
  have hρ0 : 0 < ρ := by
    have := norm_nonneg (w₀ - c)
    rw [hρdef]; linarith
  have hρR : ρ < R := by rw [hρdef]; linarith
  have hw₀ρ : ‖w₀ - c‖ < ρ := by rw [hρdef]; linarith
  have hw₀ball : w₀ ∈ ball c ρ := mem_ball_iff_norm.mpr hw₀ρ
  -- transported data on the ρ-disc
  have hhρ : ∀ n, HarmonicOnNhd (h n) (closedBall c ρ) :=
    fun n => (hh n).mono (closedBall_subset_closedBall hρR.le)
  have hcontρ : ∀ n, ContinuousOn (h n) (sphere c ρ) :=
    fun n => (hhρ n).continuousOn.mono sphere_subset_closedBall
  have huρ : TendstoUniformlyOn (fun n z => h n z) H atTop (closedBall c ρ) :=
    hunif ρ hρR
  have hHcont : ContinuousOn H (closedBall c ρ) :=
    huρ.continuousOn
      (Eventually.of_forall fun n => (hhρ n).continuousOn).frequently
  have hHsph : ContinuousOn H (sphere c ρ) :=
    hHcont.mono sphere_subset_closedBall
  have husph : TendstoUniformlyOn (fun n z => h n z) H atTop (sphere c ρ) :=
    huρ.mono sphere_subset_closedBall
  -- each member is its Poisson integral on the ρ-disc
  have hrep : ∀ n, ∀ w ∈ ball c ρ, poissonOperator (h n) c ρ w = h n w :=
    fun n w hw => (hhρ n).circleAverage_poissonKernel_smul hw
  -- the identity passes to the limit
  have hkey : ∀ w ∈ ball c ρ, poissonOperator H c ρ w = H w := by
    intro w hw
    have h1 := tendsto_poissonOperator_of_tendstoUniformlyOn hρ0 hcontρ
      hHsph husph hw
    have h2 : Tendsto (fun n => h n w) atTop (𝓝 (H w)) :=
      huρ.tendsto_at (ball_subset_closedBall hw)
    exact tendsto_nhds_unique h1 (h2.congr fun n => (hrep n w hw).symm)
  -- conclude: `H` agrees near `w₀` with the harmonic `poissonOperator H c ρ`
  have hPharm : HarmonicOnNhd (poissonOperator H c ρ) (ball c ρ) :=
    poissonOperator_harmonicOnNhd hρ0 hHsph
  have heq : poissonOperator H c ρ =ᶠ[𝓝 w₀] H := by
    filter_upwards [isOpen_ball.mem_nhds hw₀ball] with w hw
    exact hkey w hw
  exact (harmonicAt_congr_nhds heq).mp (hPharm w₀ hw₀ball)

/--
**The Harnack increasing-limit corollary, complete** (pricing doc §3.1,
row W4; the form the Perron envelope W7 consumes): an increasing
sequence of harmonic functions on a neighborhood of `closedBall c R`,
bounded at the center, converges pointwise on the open ball and
uniformly on every closed disc `closedBall c ρ` with `ρ < R`, and the
limit is harmonic on the open ball.
-/
theorem harnack_increasing_limit_harmonic {h : ℕ → ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hh : ∀ n, HarmonicOnNhd (h n) (closedBall c R))
    (hmono : ∀ z ∈ closedBall c R, Monotone fun n => h n z)
    (hbdd : BddAbove (Set.range fun n => h n c)) :
    ∃ H : ℂ → ℝ,
      (∀ z ∈ ball c R, Tendsto (fun n => h n z) atTop (𝓝 (H z))) ∧
      (∀ ρ, ρ < R →
        TendstoUniformlyOn (fun n z => h n z) H atTop (closedBall c ρ)) ∧
      HarmonicOnNhd H (ball c R) := by
  obtain ⟨H, hpt, hunif⟩ := harnack_increasing_tendstoUniformlyOn hh hmono hbdd
  exact ⟨H, hpt, hunif, harmonicOnNhd_ball_of_tendstoUniformlyOn hh hunif⟩

end JacobianChallenge.HolomorphicForms

