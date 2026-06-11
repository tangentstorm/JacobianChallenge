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

/-!
## The annuli comparison (W6 commit 2)

Core of the removable-singularity argument: a bounded harmonic function
on the punctured disc equals any disc-Dirichlet solution of its
inner-circle restriction, conditionally on the W1 maximum-principle
input.  The Dirichlet solution enters as a *hypothesis* here; the final
W6 commit instantiates it from `DiscDirichletInput` and glues the
extension.
-/

/-- The log cup is continuous away from the puncture. -/
theorem logCup_continuousOn (c : ℂ) (r ε : ℝ) :
    ContinuousOn (logCup c r ε) {c}ᶜ := by
  intro z hz
  have hz' : z ≠ c := hz
  have hne : ‖z - c‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz')
  have hnorm : ContinuousAt (fun w : ℂ => ‖w - c‖) z :=
    ((continuous_id.sub continuous_const).norm).continuousAt
  have hlog : ContinuousAt (fun w : ℂ => Real.log ‖w - c‖) z :=
    hnorm.log hne
  exact ((continuousAt_const.sub hlog).const_mul ε).continuousWithinAt

/--
ε → 0 extraction: if `a ≤ ε * K` for every positive `ε`, with `K ≥ 0`
fixed, then `a ≤ 0`.  (Searched: the ℝ-flavor of
`le_of_forall_pos_le_add` is absent from the pin — ENNReal-only.)
-/
private theorem nonpos_of_forall_pos_mul_le {a K : ℝ} (hK : 0 ≤ K)
    (h : ∀ ε : ℝ, 0 < ε → a ≤ ε * K) : a ≤ 0 := by
  rcases eq_or_lt_of_le hK with hK0 | hKpos
  · have h1 := h 1 one_pos
    rw [← hK0, mul_zero] at h1
    exact h1
  · rcases lt_or_ge 0 a with hpos | hle
    swap
    · exact hle
    · exfalso
      have hKne : K ≠ 0 := ne_of_gt hKpos
      have h2 := h (a / (2 * K)) (by positivity)
      have heq : a / (2 * K) * K = a / 2 := by
        field_simp
      rw [heq] at h2
      linarith

/--
One-sided comparison on shrinking annuli: a harmonic function on the
punctured ball, continuous up to the punctured closed ball, bounded
above, and `≤ 0` on the outer circle, lies below every positive-weight
log cup.  This is the `hMP`-consuming step of the W6 argument.
-/
private theorem le_logCup_of_sphere_nonpos
    (hMP : WeakMaxPrincipleInput) {w : ℂ → ℝ} {c : ℂ} {r B ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε)
    (hw : HarmonicOnNhd w (ball c r \ {c}))
    (hwc : ContinuousOn w (closedBall c r \ {c}))
    (hB : ∀ z ∈ closedBall c r \ {c}, w z ≤ B)
    (hsph : ∀ z ∈ sphere c r, w z ≤ 0) :
    ∀ z ∈ ball c r \ {c}, w z ≤ logCup c r ε z := by
  -- Extract a punctured δ₀-ball on which the cup dominates `B`.
  have hev : {x : ℂ | B ≤ logCup c r ε x} ∈ 𝓝[≠] c :=
    eventually_le_logCup hε B
  rw [Metric.mem_nhdsWithin_iff] at hev
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := hev
  intro z hz
  have hzball : z ∈ ball c r := hz.1
  have hznec : z ≠ c := hz.2
  have hzc_pos : 0 < ‖z - c‖ := by
    simpa [norm_pos_iff] using sub_ne_zero.mpr hznec
  have hmin : 0 < min ‖z - c‖ δ₀ := lt_min hzc_pos hδ₀pos
  set δ : ℝ := min ‖z - c‖ δ₀ / 2 with hδdef
  have hδpos : 0 < δ := by positivity
  have hδltz : δ < ‖z - c‖ :=
    (half_lt_self hmin).trans_le (min_le_left _ _)
  have hδltδ₀ : δ < δ₀ :=
    (half_lt_self hmin).trans_le (min_le_right _ _)
  have hδr : δ < r := by
    have hzr : ‖z - c‖ < r := by
      rw [← dist_eq_norm]
      exact mem_ball.mp hzball
    exact hδltz.trans hzr
  set V : Set ℂ := ball c r \ closedBall c δ with hVdef
  have hzV : z ∈ V := by
    refine ⟨hzball, ?_⟩
    simp only [mem_closedBall, not_le]
    rw [dist_eq_norm]
    exact hδltz
  have hVsub : V ⊆ ball c r \ {c} := by
    intro x hx
    refine ⟨hx.1, fun hxc => ?_⟩
    rw [Set.mem_singleton_iff] at hxc
    subst hxc
    exact hx.2 (mem_closedBall_self hδpos.le)
  -- closure control: `closure V ⊆ closedBall c r \ ball c δ`.
  have hclos : closure V ⊆ closedBall c r \ ball c δ := by
    intro x hx
    have h1 : closure V ⊆ closure (ball c r) ∩ closure ((closedBall c δ)ᶜ) := by
      rw [hVdef, Set.diff_eq]
      exact closure_inter_subset_inter_closure _ _
    have h2 := h1 hx
    rw [closure_ball c hr.ne', closure_compl,
      interior_closedBall c hδpos.ne'] at h2
    exact ⟨h2.1, h2.2⟩
  have hclos' : closure V ⊆ closedBall c r \ {c} := by
    intro x hx
    refine ⟨(hclos hx).1, fun hxc => ?_⟩
    rw [Set.mem_singleton_iff] at hxc
    subst hxc
    exact (hclos hx).2 (mem_ball_self hδpos)
  -- frontier control: both circles are good.
  have hfront : ∀ ζ ∈ frontier V, w ζ - logCup c r ε ζ ≤ 0 := by
    intro ζ hζ
    have hfr : ζ ∈ sphere c r ∪ sphere c δ := by
      have hsplit := frontier_inter_subset (ball c r) ((closedBall c δ)ᶜ)
      rw [hVdef, Set.diff_eq] at hζ
      rcases hsplit hζ with ⟨hx1, _⟩ | ⟨_, hx2⟩
      · left
        rwa [frontier_ball c hr.ne'] at hx1
      · right
        rwa [frontier_compl, frontier_closedBall c hδpos.ne'] at hx2
    rcases hfr with hsphr | hsphδ
    · have h1 := hsph ζ hsphr
      have h2 := logCup_eq_zero_of_mem_sphere ε hsphr
      linarith
    · have hζdist : dist ζ c = δ := mem_sphere.mp hsphδ
      have hζne : ζ ≠ c := by
        intro hcontra
        rw [hcontra, dist_self] at hζdist
        exact hδpos.ne hζdist
      have hζmem : ζ ∈ closedBall c r \ {c} := by
        refine ⟨mem_closedBall.mpr ?_, hζne⟩
        rw [hζdist]
        exact hδr.le
      have hBζ := hB ζ hζmem
      have hcupζ : B ≤ logCup c r ε ζ := by
        refine hδ₀ ⟨mem_ball.mpr ?_, hζne⟩
        rw [hζdist]
        exact hδltδ₀
      linarith
  -- the max-principle input on `V`.
  have happly := hMP V (fun x => w x - logCup c r ε x)
    (isOpen_ball.sdiff isClosed_closedBall)
    (isBounded_ball.subset Set.diff_subset)
    (fun x hx => (hw x (hVsub hx)).sub
      (logCup_harmonicOnNhd c r ε x (hVsub hx).2))
    (((hwc.mono hclos').sub
      ((logCup_continuousOn c r ε).mono fun x hx => (hclos' hx).2)))
    hfront
  exact sub_nonpos.mp (happly z hzV)

/--
**The annuli comparison (W6 core).**  A harmonic function on the
punctured ball `ball c R \ {c}`, bounded there, agrees on the punctured
inner ball `ball c r \ {c}` (any `r < R`) with every function that is
harmonic on `ball c r`, continuous up to the closed ball, and matches it
on `sphere c r` — conditionally on the W1 maximum-principle input.
Two applications of the one-sided log-cup comparison and `ε → 0`.
-/
theorem eq_dirichletSolution_of_bounded_punctured
    (hMP : WeakMaxPrincipleInput)
    {u h : ℂ → ℝ} {c : ℂ} {r R M : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hu : HarmonicOnNhd u (ball c R \ {c}))
    (hbd : ∀ z ∈ ball c R \ {c}, |u z| ≤ M)
    (hh : HarmonicOnNhd h (ball c r))
    (hhc : ContinuousOn h (closedBall c r))
    (hagree : Set.EqOn h u (sphere c r)) :
    Set.EqOn u h (ball c r \ {c}) := by
  -- bound `h` on the compact closed ball
  obtain ⟨Mh, hMh⟩ : ∃ Mh, ∀ x ∈ closedBall c r, |h x| ≤ Mh := by
    obtain ⟨Mh, hMh⟩ :=
      (isCompact_closedBall c r).exists_bound_of_continuousOn hhc
    exact ⟨Mh, fun x hx => by simpa [Real.norm_eq_abs] using hMh x hx⟩
  -- set inclusions
  have hsubc : closedBall c r \ {c} ⊆ ball c R \ {c} := fun x hx =>
    ⟨closedBall_subset_ball hrR hx.1, hx.2⟩
  have hsubb : ball c r \ {c} ⊆ ball c R \ {c} := fun x hx =>
    ⟨ball_subset_ball hrR.le hx.1, hx.2⟩
  -- shared ingredients for both signs
  have hwu : ContinuousOn u (closedBall c r \ {c}) :=
    (continuousOn_of_harmonicOnNhd hu).mono hsubc
  have hwh : ContinuousOn h (closedBall c r \ {c}) :=
    hhc.mono Set.diff_subset
  -- one-sided comparisons, for every positive ε
  have hside : ∀ ε : ℝ, 0 < ε → ∀ z ∈ ball c r \ {c},
      u z - h z ≤ logCup c r ε z ∧ h z - u z ≤ logCup c r ε z := by
    intro ε hε
    have h₁ := le_logCup_of_sphere_nonpos hMP hr hε
      (w := fun x => u x - h x) (B := M + Mh)
      (fun x hx => (hu x (hsubb hx)).sub (hh x hx.1))
      (hwu.sub hwh)
      (fun x hx => by
        have h1 := abs_le.mp (hbd x (hsubc hx))
        have h2 := abs_le.mp (hMh x hx.1)
        linarith [h1.2, h2.1])
      (fun x hx => by
        rw [hagree hx]
        simp)
    have h₂ := le_logCup_of_sphere_nonpos hMP hr hε
      (w := fun x => h x - u x) (B := M + Mh)
      (fun x hx => (hh x hx.1).sub (hu x (hsubb hx)))
      (hwh.sub hwu)
      (fun x hx => by
        have h1 := abs_le.mp (hbd x (hsubc hx))
        have h2 := abs_le.mp (hMh x hx.1)
        linarith [h1.1, h2.2])
      (fun x hx => by
        rw [hagree hx]
        simp)
    exact fun z hz => ⟨h₁ z hz, h₂ z hz⟩
  -- ε → 0
  intro z hz
  have hzc_pos : 0 < ‖z - c‖ := by
    simpa [norm_pos_iff] using sub_ne_zero.mpr hz.2
  have hzr : ‖z - c‖ ≤ r := by
    rw [← dist_eq_norm]
    exact (mem_ball.mp hz.1).le
  have hK : 0 ≤ Real.log r - Real.log ‖z - c‖ :=
    sub_nonneg.mpr (Real.log_le_log hzc_pos hzr)
  have hle : u z - h z ≤ 0 :=
    nonpos_of_forall_pos_mul_le hK fun ε hε => by
      simpa [logCup] using (hside ε hε z hz).1
  have hge : h z - u z ≤ 0 :=
    nonpos_of_forall_pos_mul_le hK fun ε hε => by
      simpa [logCup] using (hside ε hε z hz).2
  linarith

end JacobianChallenge.HolomorphicForms
