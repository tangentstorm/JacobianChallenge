import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-!
# Bounded-harmonic removable singularity — statements and W1-independent leaves (Perron engine B2 toolbox W6, commit 1)

Blueprint node: `lem:perron-removable-singularity`.

W6 of the B2 pricing (`docs/perron-b2-dirichlet-phase0.md` §4): a bounded
harmonic function on a punctured disc extends harmonically across the
puncture, plus the limit corollary.  Consumed by W9 (the Green's-function
pole germ, §3.3).  Proof route (§3.3): compare `±(u − h)` against the log
cup `ε·(log r − log‖z − c‖)` on shrinking annuli, where `h` solves the
disc Dirichlet problem for `u`'s restriction to an inner circle; let
`ε → 0`; glue.

This first commit lands the **named-obligation inputs** and every leaf
that does not need them, all sorry-free:

* `WeakMaxPrincipleInput` — the W1 obligation (harmonic weak maximum
  principle, closure-continuity form).  Owner lane: W1/jc10.  When the
  max principle lands, a thin adapter discharges this `Prop` by import.
* `DiscDirichletInput` — the W3 obligation (disc Dirichlet solution from
  continuous circle data; W3a–c landed in `PerronPoissonOperator.lean`,
  the boundary-limit half is W3d).  Owner lane: W3/jc6.  Spelling to be
  reconciled with the landed operator at consumption time.
* `continuousOn_of_harmonicOnNhd`, `harmonicAt_log_norm_sub`, the
  `logCup` comparison family, and the limit corollary
  `tendsto_of_harmonic_extension`.

The main extension theorem
(`harmonicOnNhd_extend_of_bounded_punctured`, consuming both inputs as
hypotheses) lands with its conditional proof in the next W6 commits; its
exact statement is fixed in `.sci/task.md` and the pricing doc.
-/

namespace JacobianChallenge.HolomorphicForms

open Filter InnerProductSpace Metric Real

open scoped Topology

/--
**W1 named obligation (owner lane: jc10's harmonic maximum principle).**
Weak maximum principle for harmonic functions on a bounded open subset of
`ℂ`, in the closure-continuity form consumed by the W6 annuli comparison:
nonpositive frontier values force nonpositivity inside.

Note `PerronStageMaxPrinciple.lean` (B3a) does **not** discharge this: it
bounds `Re f` for holomorphic `f`, and on an annulus a harmonic function
need not be globally the real part of a holomorphic function
(`Real.log ‖z‖` is the standard witness).  Replace by import + thin
adapter when the W1 lane lands.
-/
def WeakMaxPrincipleInput : Prop :=
  ∀ (V : Set ℂ) (w : ℂ → ℝ), IsOpen V → Bornology.IsBounded V →
    HarmonicOnNhd w V → ContinuousOn w (closure V) →
    (∀ ζ ∈ frontier V, w ζ ≤ 0) →
    ∀ z ∈ V, w z ≤ 0

/--
**W3 named obligation (owner lane: jc6's Poisson operator).**
Solvability of the disc Dirichlet problem for continuous boundary data:
a function harmonic on the open ball, continuous on the closed ball,
agreeing with the data on the sphere.  The harmonic-interior half is
W3a–c (`PerronPoissonOperator.lean`); the boundary-attainment half is
W3d.  Reconcile this spelling with the landed operator names at
consumption time.
-/
def DiscDirichletInput : Prop :=
  ∀ (c : ℂ) (r : ℝ), 0 < r → ∀ g : ℂ → ℝ,
    ContinuousOn g (sphere c r) →
    ∃ h : ℂ → ℝ, HarmonicOnNhd h (ball c r) ∧
      ContinuousOn h (closedBall c r) ∧
      Set.EqOn h g (sphere c r)

/--
Harmonic functions (in the pointwise-neighborhood sense) are continuous
on their set: `HarmonicAt` contains `ContDiffAt ℝ 2`.
-/
theorem continuousOn_of_harmonicOnNhd {u : ℂ → ℝ} {s : Set ℂ}
    (hu : HarmonicOnNhd u s) : ContinuousOn u s :=
  fun z hz => (hu z hz).1.continuousAt.continuousWithinAt

/--
`log ‖z − c‖` is harmonic away from `c` — the fundamental-solution leaf
behind the log cup, from `AnalyticAt.harmonicAt_log_norm` applied to the
affine map `z ↦ z − c`.
-/
theorem harmonicAt_log_norm_sub {c z : ℂ} (hz : z ≠ c) :
    HarmonicAt (fun w => Real.log ‖w - c‖) z := by
  have h₁ : AnalyticAt ℂ (fun w : ℂ => w - c) z :=
    analyticAt_id.sub analyticAt_const
  have h₂ : z - c ≠ 0 := sub_ne_zero.mpr hz
  exact h₁.harmonicAt_log_norm h₂

/--
The **log cup** at `c` with outer radius `r` and weight `ε`:
`ε · (log r − log ‖z − c‖)`.  It vanishes on the circle `‖z − c‖ = r`,
is nonnegative inside it, is harmonic off `c`, and blows up at `c` —
the comparison majorant of the W6 annuli argument (pricing doc §3.3).
-/
noncomputable def logCup (c : ℂ) (r ε : ℝ) (z : ℂ) : ℝ :=
  ε * (Real.log r - Real.log ‖z - c‖)

/-- The log cup is harmonic away from the puncture. -/
theorem logCup_harmonicOnNhd (c : ℂ) (r ε : ℝ) :
    HarmonicOnNhd (logCup c r ε) {c}ᶜ := by
  intro z hz
  have hlog : HarmonicAt (fun w => Real.log ‖w - c‖) z :=
    harmonicAt_log_norm_sub (Set.mem_compl_singleton_iff.mp hz)
  have hsub : HarmonicAt (fun w => Real.log r - Real.log ‖w - c‖) z :=
    (harmonicAt_const (Real.log r)).sub hlog
  have hsmul := hsub.const_smul (c := ε)
  have hfun : logCup c r ε = ε • fun w => Real.log r - Real.log ‖w - c‖ := by
    funext w
    simp [logCup, smul_eq_mul]
  rw [hfun]
  exact hsmul

/-- The log cup vanishes on the outer circle. -/
theorem logCup_eq_zero_of_mem_sphere {c : ℂ} {r : ℝ} (ε : ℝ) {z : ℂ}
    (hz : z ∈ sphere c r) :
    logCup c r ε z = 0 := by
  have hnorm : ‖z - c‖ = r := by
    simpa [dist_eq_norm] using mem_sphere.mp hz
  simp [logCup, hnorm]

/-- The log cup is nonnegative on the punctured closed disc. -/
theorem logCup_nonneg {ε : ℝ} (hε : 0 ≤ ε) {c z : ℂ} {r : ℝ}
    (hz : z ≠ c) (hzr : ‖z - c‖ ≤ r) :
    0 ≤ logCup c r ε z := by
  have hpos : 0 < ‖z - c‖ := by
    simpa [norm_pos_iff] using sub_ne_zero.mpr hz
  have hlog : Real.log ‖z - c‖ ≤ Real.log r :=
    Real.log_le_log hpos hzr
  exact mul_nonneg hε (sub_nonneg.mpr hlog)

/--
The log cup beats any constant near the puncture: for positive weight
and radius, `M ≤ logCup c r ε z` for all `z ≠ c` close enough to `c`.
This is the "member-dependent cap" step of the annuli comparison — the
inner-circle boundary control comes for free from boundedness once the
cup has climbed past `2M`.
-/
theorem eventually_le_logCup {c : ℂ} {r ε : ℝ} (hε : 0 < ε) (M : ℝ) :
    ∀ᶠ z in 𝓝[≠] c, M ≤ logCup c r ε z := by
  have hnorm0 : Tendsto (fun z : ℂ => ‖z - c‖) (𝓝 c) (𝓝 0) := by
    have h1 : Tendsto (fun z : ℂ => z - c) (𝓝 c) (𝓝 (c - c)) :=
      (continuous_id.sub continuous_const).tendsto c
    rw [sub_self] at h1
    simpa using h1.norm
  have hnorm : Tendsto (fun z : ℂ => ‖z - c‖) (𝓝[≠] c) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact hnorm0.mono_left nhdsWithin_le_nhds
    · filter_upwards [eventually_mem_nhdsWithin] with z hz
      exact Set.mem_Ioi.mpr (by simpa [norm_pos_iff] using sub_ne_zero.mpr hz)
  have hlog : Tendsto (fun z : ℂ => Real.log ‖z - c‖) (𝓝[≠] c) atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hnorm
  have hcup : Tendsto (fun z : ℂ => logCup c r ε z) (𝓝[≠] c) atTop := by
    have hneg : Tendsto (fun z : ℂ => -Real.log ‖z - c‖) (𝓝[≠] c) atTop :=
      tendsto_neg_atBot_atTop.comp hlog
    have hdiff : Tendsto (fun z : ℂ => Real.log r - Real.log ‖z - c‖)
        (𝓝[≠] c) atTop := by
      simpa [sub_eq_add_neg] using
        tendsto_atTop_add_const_left (𝓝[≠] c) (Real.log r) hneg
    simpa [logCup] using hdiff.const_mul_atTop hε
  exact hcup.eventually_ge_atTop M

/--
**Limit corollary shape (W1/W3-independent).**  Once the extension
exists — `v` harmonic on the ball agreeing with `u` off the puncture —
the original function has a limit at the puncture, namely `v c`.  The
later W6 commits instantiate this with the extension produced by the
annuli comparison.
-/
theorem tendsto_of_harmonic_extension {u v : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hv : HarmonicOnNhd v (ball c R))
    (heq : Set.EqOn v u (ball c R \ {c})) :
    Tendsto u (𝓝[ball c R \ {c}] c) (𝓝 (v c)) := by
  have hc : c ∈ ball c R := mem_ball_self hR
  have hcont : ContinuousWithinAt v (ball c R \ {c}) c :=
    (hv c hc).1.continuousAt.continuousWithinAt
  have hev : v =ᶠ[𝓝[ball c R \ {c}] c] u :=
    eventually_mem_nhdsWithin.mono fun z hz => heq hz
  exact hcont.tendsto.congr' hev

end JacobianChallenge.HolomorphicForms
