import Jacobian.HolomorphicForms.PerronEnvelope

/-!
# Per-pole Perron family and the Green's-function candidate (B2 assembly W9, slice G1)

Blueprint nodes: `def:perron-greens-family`,
`lem:perron-greens-family-basics`,
`lem:perron-greens-candidate-pole-profile`.

W9 of the B2 assembly (`docs/perron-b2-dirichlet-phase0.md` §3.3 + §4):
the Green's function `G_Ω(·, p)` as the Perron envelope of the family of
comparison subfunctions with a logarithmic pole floor at `p`.  This file
is the slice-1 statement layer, ℂ-side and disc/stage-local in the
toolbox style: the family `greensFamily V p` with its closure and
membership basics (sorry-free), the envelope `greensCandidate V p`
through the frozen `perronEnvelope`, and the named frontier statements.
Slice G2 added the comparison-subclass maximum principle
(`PerronSubOn.le_zero_of_eventually_frontier_le`) and discharged the
uniform upper cap and the two-sided pole profile; the
Poisson-modification capability, the off-pole harmonicity, and the
W6-germ corollary remain declared `sorry`s priced into slices G3–G4.

## Design

* **Boundary clause in eventual form**, not `limsup`:
  `∀ ζ ∈ frontier V, ∀ ε > 0, ∀ᶠ z in 𝓝[V \ {p}] ζ, v z ≤ ε` — the §3.3
  "limsup ≤ 0 at every frontier point", but `max`-closing by filter
  intersection with no `limsup` boundedness side conditions.  (W8 is
  dropped: nothing here promises boundary *attainment*; the clause is
  only the family's one-sided trap.)
* **Pole cap** `∃ C, ∀ᶠ z in 𝓝[≠] p, v z + log ‖z - p‖ ≤ C` — §3.3's
  "`v + ℓ_p` bounded above near `p`" with `ℓ_p` in the canonical planar
  shape; chart-profile reconciliation is W10's germ-constant
  bookkeeping.
* **The explicit member reuses the W6 `logCup`**: with weight `1`,
  `logCup p ρ 1 = log ρ - log ‖· - p‖ = -ℓ_p + log ρ`, so §3.3's
  truncated log cap is `truncatedLogCap p ρ = max (logCup p ρ 1) 0`,
  inheriting the landed `logCup` API.
* **W7-ii is consumed as the named obligation**
  `PerronEnvelopeHarmonicInput` (W7-i's exact hypothesis list,
  conclusion upgraded from center-touch to harmonic-throughout),
  following the `WeakMaxPrincipleInput` convention; jc11's W7-ii lane
  discharges it by thin adapter.  The W1 and W3 obligations are already
  discharged on the branch (`weakMaxPrincipleInput_holds`,
  `discDirichletInput_of_poissonOperator`), so — per the W1 adapter
  sweep — the declarations here are hypothesis-free with respect to
  them.

Members are total functions `ℂ → ℝ` (the `perronEnvelope` junk
convention); every membership constraint lives on `V \ {p}`, and
`greensCandidate` carries meaning there only.
-/

namespace JacobianChallenge.HolomorphicForms

open Filter InnerProductSpace Metric

open scoped Topology

/--
**The per-pole Perron family `𝔉_p` (B2 assembly W9, §3.3).**  For an
open (stage-local) domain `V ⊆ ℂ` and pole `p`, the family of
comparison subfunctions from which the Green's function arises:
`PerronSubOn` members of the punctured domain that are eventually
`≤ ε` at every frontier point (the boundary trap, in `limsup`-free
eventual form) and whose shift by the log profile `log ‖· - p‖` is
bounded above near the pole (the member-dependent pole cap).
-/
def greensFamily (V : Set ℂ) (p : ℂ) : Set (ℂ → ℝ) :=
  { v | PerronSubOn v (V \ {p}) ∧
        (∀ ζ ∈ frontier V, ∀ ε : ℝ, 0 < ε →
          ∀ᶠ z in 𝓝[V \ {p}] ζ, v z ≤ ε) ∧
        (∃ C : ℝ, ∀ᶠ z in 𝓝[≠] p, v z + Real.log ‖z - p‖ ≤ C) }

/--
**Max-closure of the Green's family (W9 G1).**  The pointwise maximum
of two members is a member: `PerronSubOn.max` closes the comparison
clause, the boundary and pole clauses close by intersecting the
eventual sets (`max C₁ C₂` caps the maximum).  The statement shape is
the `hmax` field of the W7 envelope hypotheses, verbatim.
-/
theorem greensFamily_max_mem {V : Set ℂ} {p : ℂ} {v₁ v₂ : ℂ → ℝ}
    (h₁ : v₁ ∈ greensFamily V p) (h₂ : v₂ ∈ greensFamily V p) :
    (fun z => max (v₁ z) (v₂ z)) ∈ greensFamily V p := by
  obtain ⟨hs₁, hf₁, C₁, hC₁⟩ := h₁
  obtain ⟨hs₂, hf₂, C₂, hC₂⟩ := h₂
  refine ⟨hs₁.max hs₂, fun ζ hζ ε hε => ?_, max C₁ C₂, ?_⟩
  · filter_upwards [hf₁ ζ hζ ε hε, hf₂ ζ hζ ε hε] with z hz₁ hz₂
    exact max_le hz₁ hz₂
  · filter_upwards [hC₁, hC₂] with z hz₁ hz₂
    rw [show max (v₁ z) (v₂ z) + Real.log ‖z - p‖ =
        max (v₁ z + Real.log ‖z - p‖) (v₂ z + Real.log ‖z - p‖) from
      (max_add_add_right _ _ _).symm]
    exact max_le (hz₁.trans (le_max_left _ _)) (hz₂.trans (le_max_right _ _))

/--
The zero function is a member: harmonic (hence a `PerronSubOn` member
via the W1-discharged `of_harmonicOnNhd'`), trapped at the boundary
(`0 ≤ ε`), and capped at the pole with `C = 0` since
`log ‖z - p‖ ≤ 0` once `‖z - p‖ ≤ 1`.  Gives nonemptiness with **no**
geometric hypotheses, and the `≥ 0` floor of the envelope.
-/
theorem zero_mem_greensFamily {V : Set ℂ} {p : ℂ} :
    (fun _ => (0 : ℝ)) ∈ greensFamily V p := by
  refine ⟨PerronSubOn.of_harmonicOnNhd' fun z _ => harmonicAt_const 0,
    fun ζ _ ε hε => Eventually.of_forall fun z => hε.le, 0, ?_⟩
  have h1 : ∀ᶠ z in 𝓝 p, z ∈ ball p 1 :=
    isOpen_ball.eventually_mem (mem_ball_self one_pos)
  filter_upwards [h1.filter_mono nhdsWithin_le_nhds] with z hz
  have h2 : ‖z - p‖ ≤ 1 := by
    rw [← dist_eq_norm]
    exact (mem_ball.mp hz).le
  simpa using Real.log_nonpos (norm_nonneg _) h2

/-- The Green's family is nonempty (the zero member). -/
theorem greensFamily_nonempty {V : Set ℂ} {p : ℂ} :
    (greensFamily V p).Nonempty :=
  ⟨_, zero_mem_greensFamily⟩

/--
**The truncated log cap (§3.3's explicit member).**  The W6 log cup at
weight `1` truncated at `0`: `max (log ρ - log ‖· - p‖) 0`.  Inside the
disc `ball p ρ` it is the harmonic log profile shifted to vanish on the
bounding circle; outside it is `0` — the `max` *is* the seam gluing.
-/
noncomputable def truncatedLogCap (p : ℂ) (ρ : ℝ) : ℂ → ℝ :=
  fun z => max (logCup p ρ 1 z) 0

/-- The weight-`1` log cup, evaluated. -/
theorem logCup_one_apply (p : ℂ) (ρ : ℝ) (z : ℂ) :
    logCup p ρ 1 z = Real.log ρ - Real.log ‖z - p‖ := by
  simp [logCup]

/--
**The truncated log cap is a member (W9 G1, §3.3 nonemptiness with the
right lower profile).**  For a comparison disc `closedBall p ρ ⊆ V`:

* `PerronSubOn (V \ {p})`: the cap is the `max` of the two harmonic
  members `logCup p ρ 1` (harmonic off the pole, W6 leaf) and `0`;
* boundary trap: every frontier point is outside `closedBall p ρ`
  (`V` is open), where the cup is negative and the cap is `0 ≤ ε`;
* pole cap, with the **exact** constant `log ρ`: inside the punctured
  disc the cap is the cup and
  `truncatedLogCap p ρ z + log ‖z - p‖ = log ρ`.

The exactness is what feeds the envelope's pole lower bound
(`log_le_greensCandidate_add_log`).
-/
theorem truncatedLogCap_mem_greensFamily {V : Set ℂ} {p : ℂ} {ρ : ℝ}
    (hV : IsOpen V) (hρ : 0 < ρ) (hsub : Metric.closedBall p ρ ⊆ V) :
    truncatedLogCap p ρ ∈ greensFamily V p := by
  refine ⟨?_, ?_, Real.log ρ, ?_⟩
  · -- the comparison clause: max of two harmonic members
    have hlog : PerronSubOn (logCup p ρ 1) (V \ {p}) :=
      PerronSubOn.of_harmonicOnNhd'
        ((logCup_harmonicOnNhd p ρ 1).mono fun z hz => hz.2)
    have hzero : PerronSubOn (fun _ => (0 : ℝ)) (V \ {p}) :=
      PerronSubOn.of_harmonicOnNhd' fun z _ => harmonicAt_const 0
    exact hlog.max hzero
  · -- the boundary trap: the cap vanishes near every frontier point
    intro ζ hζ ε hε
    have hζV : ζ ∉ V := by
      rw [hV.frontier_eq] at hζ
      exact hζ.2
    have hζU : ζ ∈ (Metric.closedBall p ρ)ᶜ := fun hc => hζV (hsub hc)
    have hU : ∀ᶠ z in 𝓝 ζ, z ∈ (Metric.closedBall p ρ)ᶜ :=
      Metric.isClosed_closedBall.isOpen_compl.eventually_mem hζU
    filter_upwards [hU.filter_mono nhdsWithin_le_nhds] with z hz
    have hzρ : ρ < ‖z - p‖ := by
      rw [← dist_eq_norm]
      exact lt_of_not_ge fun h => hz (Metric.mem_closedBall.mpr h)
    have hneg : logCup p ρ 1 z < 0 := by
      rw [logCup_one_apply]
      exact sub_neg.mpr (Real.log_lt_log hρ hzρ)
    calc truncatedLogCap p ρ z = 0 := max_eq_right hneg.le
      _ ≤ ε := hε.le
  · -- the pole cap, with the exact constant log ρ
    have hball : ∀ᶠ z in 𝓝 p, z ∈ ball p ρ :=
      isOpen_ball.eventually_mem (mem_ball_self hρ)
    filter_upwards [hball.filter_mono nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin] with z hz hzne
    have hzp : z ≠ p := hzne
    have hzρ : ‖z - p‖ ≤ ρ := by
      rw [← dist_eq_norm]
      exact (Metric.mem_ball.mp hz).le
    have hcup : 0 ≤ logCup p ρ 1 z := logCup_nonneg one_pos.le hzp hzρ
    show max (logCup p ρ 1 z) 0 + Real.log ‖z - p‖ ≤ Real.log ρ
    rw [max_eq_left hcup, logCup_one_apply]
    linarith

/--
**The Green's-function candidate (W9, §3.3): `G_p := sup 𝔉_p`**, through
the frozen `perronEnvelope`.  Meaningful on `V \ {p}` (junk elsewhere,
per the envelope's `sSup` convention).
-/
noncomputable def greensCandidate (V : Set ℂ) (p : ℂ) : ℂ → ℝ :=
  perronEnvelope (greensFamily V p)

/--
The candidate is nonnegative on the punctured domain: the zero member
sits below the envelope wherever the family is pointwise bounded
(`hbdd` is discharged by `greensFamily_bddAbove` once the G2 cap
lands).
-/
theorem greensCandidate_nonneg {V : Set ℂ} {p : ℂ}
    (hbdd : ∀ z ∈ V \ {p}, BddAbove ((fun v => v z) '' greensFamily V p)) :
    ∀ z ∈ V \ {p}, 0 ≤ greensCandidate V p z := fun z hz =>
  le_perronEnvelope zero_mem_greensFamily (hbdd z hz)

/--
**Pole lower profile (W9 G1, the lower half of the two-sided §3.3
profile).**  Near the pole the envelope dominates the truncated log
cap, whose shifted value is exactly `log ρ`:
`log ρ ≤ greensCandidate V p z + log ‖z - p‖` eventually at `p`.  The
upper half is the G2 statement `greensCandidate_pole_profile`.
-/
theorem log_le_greensCandidate_add_log {V : Set ℂ} {p : ℂ} {ρ : ℝ}
    (hV : IsOpen V) (hρ : 0 < ρ) (hsub : Metric.closedBall p ρ ⊆ V)
    (hbdd : ∀ z ∈ V \ {p}, BddAbove ((fun v => v z) '' greensFamily V p)) :
    ∀ᶠ z in 𝓝[≠] p,
      Real.log ρ ≤ greensCandidate V p z + Real.log ‖z - p‖ := by
  have hmem := truncatedLogCap_mem_greensFamily hV hρ hsub
  have hball : ∀ᶠ z in 𝓝 p, z ∈ ball p ρ :=
    isOpen_ball.eventually_mem (mem_ball_self hρ)
  filter_upwards [hball.filter_mono nhdsWithin_le_nhds,
    eventually_mem_nhdsWithin] with z hz hzne
  have hzp : z ≠ p := hzne
  have hzV : z ∈ V \ {p} := ⟨hsub (ball_subset_closedBall hz), hzp⟩
  have h1 : truncatedLogCap p ρ z ≤ greensCandidate V p z :=
    le_perronEnvelope hmem (hbdd z hzV)
  have hzρ : ‖z - p‖ ≤ ρ := by
    rw [← dist_eq_norm]
    exact (Metric.mem_ball.mp hz).le
  have hcup : 0 ≤ logCup p ρ 1 z := logCup_nonneg one_pos.le hzp hzρ
  have h2 : truncatedLogCap p ρ z = Real.log ρ - Real.log ‖z - p‖ := by
    show max (logCup p ρ 1 z) 0 = _
    rw [max_eq_left hcup, logCup_one_apply]
  linarith

/-!
## The W7-ii named obligation
-/

/--
**W7-ii obligation (owner lane: jc11's Perron envelope, in flight).**
Perron's lemma, second-comparison form: under W7-i's exact hypothesis
list — nonempty, `max`-closed, pointwise bounded family with the
Poisson-modification capability on a disc `closedBall c R ⊆ V` — the
envelope itself is harmonic on the open disc.  This upgrades the landed
center-touch core `perronEnvelope_exists_harmonic_eq_at` from "touches
a harmonic minorant at each point" to "is harmonic throughout"; when
jc11's W7-ii lands, a thin adapter discharges this `Prop` by import,
per the `WeakMaxPrincipleInput` convention.
-/
def PerronEnvelopeHarmonicInput : Prop :=
  ∀ (F : Set (ℂ → ℝ)) (V : Set ℂ) (c : ℂ) (R : ℝ),
    F.Nonempty →
    (∀ v₁ ∈ F, ∀ v₂ ∈ F, (fun z => max (v₁ z) (v₂ z)) ∈ F) →
    (∀ z ∈ V, BddAbove ((fun v => v z) '' F)) →
    0 < R → Metric.closedBall c R ⊆ V →
    PoissonModificationInput F V c R →
    HarmonicOnNhd (perronEnvelope F) (Metric.ball c R)

/-!
## The comparison-subclass maximum principle (W9 G2)

The cap proof needs a weak maximum principle for `PerronSubOn` members
with *eventual* boundary control — the landed W1
(`le_zero_of_harmonicOnNhd_of_frontier_le_zero`) does not apply, since
members are not continuous up to `closure W` and the Green's family's
boundary trap is eventual, not pointwise-on-frontier.  The proof
mirrors the W1 M2 component skeleton, with the harmonic mean-value
property replaced by the Poisson sub-mean inequality for members
(`le_poissonSolution_of_mem_ball` at the center, where the Poisson
kernel is constantly `1`).
-/

/-- The Poisson kernel at the center of the circle is `1`. -/
private theorem poissonKernel_center {c z : ℂ} {R : ℝ} (hR : 0 < R)
    (hz : z ∈ sphere c R) : poissonKernel c c z = 1 := by
  have hnorm : ‖z - c‖ = R := by
    simpa [dist_eq_norm] using mem_sphere.mp hz
  have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR.ne'
  rw [poissonKernel_def, sub_self, norm_zero, sub_zero, hnorm]
  rw [show (0 : ℝ) ^ 2 = 0 by norm_num, sub_zero, div_self hR2]

/--
The Poisson operator at the center of the disc is the plain circle
average of the boundary datum (the kernel is `1` on the circle).
-/
theorem poissonOperator_center {φ : ℂ → ℝ} {c : ℂ} {R : ℝ} (hR : 0 < R) :
    poissonOperator φ c R c = Real.circleAverage φ c R := by
  have h : poissonOperator φ c R c
      = Real.circleAverage (fun z => poissonKernel c c z • φ z) c R := rfl
  rw [h]
  apply Real.circleAverage_congr_sphere
  intro z hz
  rw [abs_of_pos hR] at hz
  simp [poissonKernel_center hR hz]

/--
**Sub-mean inequality for comparison members** — the surrogate for the
harmonic mean-value property: on any disc inside the domain, a member's
center value is at most its circle average.  Via the W5b-iii comparison
half `le_poissonSolution_of_mem_ball` evaluated at the center.
-/
theorem PerronSubOn.le_circleAverage {v : ℂ → ℝ} {W : Set ℂ}
    (hv : PerronSubOn v W) {x : ℂ} {r : ℝ} (hr : 0 < r)
    (hsub : Metric.closedBall x r ⊆ W) :
    v x ≤ Real.circleAverage v x r := by
  have h1 : v x ≤ poissonSolution v x r x :=
    hv.le_poissonSolution_of_mem_ball hr hsub x (mem_ball_self hr)
  rwa [poissonSolution_apply_of_mem_ball (mem_ball_self hr),
    poissonOperator_center hr] at h1

/--
**Local maximum propagation for comparison members**: a member of
`PerronSubOn W` attaining its global maximum over `W` at `x` is
constant on every closed disc `closedBall x r ⊆ W`.  Per concentric
circle: the sub-mean inequality squeezes the circle average up to the
maximum value, and the W1 rigidity lemma
`eq_const_sphere_of_circleAverage_eq_of_le` upgrades the squeeze to
pointwise equality.
-/
theorem PerronSubOn.eq_const_closedBall_of_le {v : ℂ → ℝ} {W : Set ℂ}
    (hv : PerronSubOn v W) {x : ℂ} {r : ℝ}
    (hsub : Metric.closedBall x r ⊆ W)
    (hle : ∀ z ∈ W, v z ≤ v x) :
    ∀ z ∈ Metric.closedBall x r, v z = v x := by
  intro z hz
  rcases eq_or_ne z x with rfl | hzx
  · rfl
  have hρ : 0 < dist z x := dist_pos.mpr hzx
  have hρr : dist z x ≤ r := mem_closedBall.mp hz
  have hsub' : Metric.closedBall x (dist z x) ⊆ W :=
    (closedBall_subset_closedBall hρr).trans hsub
  have hsph : sphere x (dist z x) ⊆ W :=
    sphere_subset_closedBall.trans hsub'
  have hcont : ContinuousOn v (sphere x (dist z x)) :=
    hv.continuousOn.mono hsph
  have h1 : v x ≤ Real.circleAverage v x (dist z x) :=
    hv.le_circleAverage hρ hsub'
  have h2 : Real.circleAverage v x (dist z x) ≤ v x := by
    refine Real.circleAverage_mono_on_of_le_circle
      (ContinuousOn.circleIntegrable hρ.le hcont) fun ζ hζ => ?_
    rw [abs_of_pos hρ] at hζ
    exact hle ζ (hsph hζ)
  exact eq_const_sphere_of_circleAverage_eq_of_le hρ hcont
    (fun ζ hζ => hle ζ (hsph hζ)) (le_antisymm h2 h1) z (mem_sphere.mpr rfl)

/--
Removing an interior point adds it to the frontier:
`frontier (V \ {p}) = frontier V ∪ {p}` for `V` open, `p ∈ V`.
-/
private theorem frontier_diff_singleton {V : Set ℂ} {p : ℂ}
    (hV : IsOpen V) (hp : p ∈ V) :
    frontier (V \ {p}) = frontier V ∪ {p} := by
  have hopen : IsOpen (V \ {p}) := hV.sdiff isClosed_singleton
  have hpcl : p ∈ closure (V \ {p}) := by
    rw [mem_closure_iff_nhdsWithin_neBot]
    have heq : 𝓝[V \ {p}] p = 𝓝[≠] p := by
      rw [Set.diff_eq, Set.inter_comm]
      exact (nhdsWithin_restrict' _ (hV.mem_nhds hp)).symm
    rw [heq]
    exact inferInstance
  have hclos : closure (V \ {p}) = closure V := by
    refine Set.Subset.antisymm (closure_mono Set.diff_subset) ?_
    refine closure_minimal ?_ isClosed_closure
    intro w hwV
    rcases eq_or_ne w p with rfl | hwp
    · exact hpcl
    · exact subset_closure ⟨hwV, hwp⟩
  rw [hopen.frontier_eq, hV.frontier_eq, hclos]
  ext ζ
  simp only [Set.mem_diff, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases hζp : ζ = p
    · exact Or.inr hζp
    · exact Or.inl ⟨h1, fun hζV => h2 ⟨hζV, hζp⟩⟩
  · rintro (⟨h1, h2⟩ | rfl)
    · exact ⟨h1, fun hmem => h2 hmem.1⟩
    · exact ⟨subset_closure hp, fun hmem => hmem.2 rfl⟩

/--
ε → 0 extraction: if `a ≤ ε * K` for every positive `ε`, with `K ≥ 0`
fixed, then `a ≤ 0`.  (Local copy — the W6 original in
`PerronRemovableSingularity.lean` is `private`; the ℝ-flavor of
`le_of_forall_pos_le_add` is absent from the pin.)
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
**Weak maximum principle for the comparison subclass, eventual-boundary
form (W9 G2 provider).**  A `PerronSubOn` member of a bounded open
`W ⊆ ℂ` that is eventually `≤ ε` at every frontier point (for every
`ε > 0`) is nonpositive throughout `W`.

This is the form the Green's family consumes: members are continuous on
`W` only (not up to the closure), and their boundary control is the
eventual trap.  Proof: for fixed `ε`, the trap sets cover the frontier
by an open `G` with `u ≤ ε` on `G ∩ W`; off `G` the maximum over the
compact `closure W \ G ⊆ W` is attained and — if it exceeded `ε` —
would be the global maximum over `W`, whose level set is open by the
member local-max propagation and closed by continuity, hence contains a
whole connected component; the bounded component's closure exits it at
a frontier point of `W`, where the trap on the `NeBot` within-filter
forces the maximum `≤ ε`.  Mirrors the W1 M2 component skeleton
(`le_zero_of_harmonicOnNhd_of_frontier_le_zero`).
-/
theorem PerronSubOn.le_zero_of_eventually_frontier_le {W : Set ℂ}
    {u : ℂ → ℝ} (hW : IsOpen W) (hWb : Bornology.IsBounded W)
    (hu : PerronSubOn u W)
    (hfr : ∀ ζ ∈ frontier W, ∀ ε : ℝ, 0 < ε → ∀ᶠ z in 𝓝[W] ζ, u z ≤ ε) :
    ∀ z ∈ W, u z ≤ 0 := by
  -- the quantitative claim: u ≤ ε on W for every positive ε
  have hmain : ∀ ε : ℝ, 0 < ε → ∀ y ∈ W, u y ≤ ε := by
    intro ε hε y hyW
    by_contra hy
    rw [not_le] at hy
    -- the trap sets, packaged as one open set ⊇ frontier W
    set T : Set ℂ := {w : ℂ | w ∈ W → u w ≤ ε} with hT
    have hfrT : frontier W ⊆ interior T := by
      intro ζ hζ
      rw [mem_interior_iff_mem_nhds]
      have h := hfr ζ hζ ε hε
      rw [eventually_nhdsWithin_iff] at h
      exact Filter.eventually_iff.mp h
    -- the off-trap core K is compact and sits inside W
    have hKclosed : IsClosed (closure W \ interior T) :=
      isClosed_closure.sdiff isOpen_interior
    have hKcpt : IsCompact (closure W \ interior T) :=
      hWb.isCompact_closure.of_isClosed_subset hKclosed Set.diff_subset
    have hKW : closure W \ interior T ⊆ W := by
      intro w hw
      by_cases hwW : w ∈ W
      · exact hwW
      · exact absurd (hfrT (by rw [hW.frontier_eq]; exact ⟨hw.1, hwW⟩)) hw.2
    -- the maximum over K is the global maximum over W
    have hyK : y ∈ closure W \ interior T := by
      refine ⟨subset_closure hyW, fun hyT => ?_⟩
      have : u y ≤ ε := (interior_subset hyT) hyW
      linarith
    obtain ⟨x₀, hx₀K, hmaxK⟩ :=
      hKcpt.exists_isMaxOn ⟨y, hyK⟩ (hu.continuousOn.mono hKW)
    have hεm : ε < u x₀ := lt_of_lt_of_le hy (hmaxK hyK)
    have hWle : ∀ w ∈ W, u w ≤ u x₀ := by
      intro w hwW
      by_cases hwT : w ∈ interior T
      · exact le_trans ((interior_subset hwT) hwW) hεm.le
      · exact hmaxK ⟨subset_closure hwW, hwT⟩
    -- the maximum propagates over the whole connected component
    have hx₀W : x₀ ∈ W := hKW hx₀K
    set U := connectedComponentIn W x₀ with hU
    have hUW : U ⊆ W := connectedComponentIn_subset W x₀
    have hUopen : IsOpen U := hW.connectedComponentIn
    have hx₀U : x₀ ∈ U := mem_connectedComponentIn hx₀W
    set A : Set ℂ := {ζ ∈ U | u ζ = u x₀} with hA
    have hAopen : IsOpen A := by
      rw [Metric.isOpen_iff]
      rintro a ⟨haU, haM⟩
      obtain ⟨ρ', hρ'pos, hball⟩ :=
        nhds_basis_closedBall.mem_iff.mp (hW.mem_nhds (hUW haU))
      have hconst : ∀ ζ ∈ Metric.closedBall a ρ', u ζ = u a := by
        refine hu.eq_const_closedBall_of_le hball fun ζ hζ => ?_
        rw [haM]
        exact hWle ζ hζ
      have hballW : ball a ρ' ⊆ W := fun w hw => hball (ball_subset_closedBall hw)
      have hpc : IsPreconnected (ball a ρ') := (convex_ball a ρ').isPreconnected
      have hballU : ball a ρ' ⊆ U := by
        rw [hU, connectedComponentIn_eq haU]
        exact hpc.subset_connectedComponentIn (mem_ball_self hρ'pos) hballW
      exact ⟨ρ', hρ'pos, fun ζ hζ =>
        ⟨hballU hζ, (hconst ζ (ball_subset_closedBall hζ)).trans haM⟩⟩
    have hUA : U ⊆ A := by
      refine isPreconnected_connectedComponentIn.subset_of_closure_inter_subset
        hAopen ⟨x₀, hx₀U, hx₀U, rfl⟩ ?_
      rintro ζ ⟨hζcl, hζU⟩
      haveI : (𝓝[A] ζ).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hζcl
      have hAW : A ⊆ W := fun w hw => hUW hw.1
      have h1 : Tendsto u (𝓝[A] ζ) (𝓝 (u ζ)) :=
        ((hu.continuousOn ζ (hUW hζU)).mono hAW).tendsto
      have h2 : Tendsto u (𝓝[A] ζ) (𝓝 (u x₀)) := by
        refine Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [self_mem_nhdsWithin] with w hw
        exact hw.2.symm
      exact ⟨hζU, tendsto_nhds_unique h1 h2⟩
    -- the bounded component is not clopen, so its closure leaves it ...
    obtain ⟨ζ, hζcl, hζU⟩ : ∃ ζ, ζ ∈ closure U ∧ ζ ∉ U := by
      by_contra h
      push Not at h
      rcases isClopen_iff.mp ⟨isClosed_of_closure_subset h, hUopen⟩ with h0 | huniv
      · exact (h0 ▸ hx₀U : x₀ ∈ (∅ : Set ℂ)).elim
      · exact NormedSpace.unbounded_univ ℝ ℂ (huniv ▸ hWb.subset hUW)
    -- ... and the exit point is outside W, hence on the frontier
    have hζW : ζ ∉ W := by
      intro hζW
      obtain ⟨w', hw'C, hw'U⟩ :=
        mem_closure_iff.mp hζcl _ hW.connectedComponentIn
          (mem_connectedComponentIn hζW)
      apply hζU
      have hUeq : connectedComponentIn W x₀ = connectedComponentIn W ζ :=
        (connectedComponentIn_eq hw'U).trans (connectedComponentIn_eq hw'C).symm
      rw [hU, hUeq]
      exact mem_connectedComponentIn hζW
    have hζfr : ζ ∈ frontier W := by
      rw [hW.frontier_eq]
      exact ⟨closure_mono hUW hζcl, hζW⟩
    -- the trap meets the maximum value on a NeBot within-filter
    haveI : (𝓝[U] ζ).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hζcl
    have h1 : ∀ᶠ w in 𝓝[U] ζ, u w ≤ ε :=
      (hfr ζ hζfr ε hε).filter_mono (nhdsWithin_mono ζ hUW)
    have h2 : ∀ᶠ w in 𝓝[U] ζ, u w = u x₀ := by
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact (hUA hw).2
    obtain ⟨w, hw1, hw2⟩ := (h1.and h2).exists
    rw [hw2] at hw1
    linarith
  -- ε → 0
  intro z hz
  by_contra h
  rw [not_le] at h
  have := hmain (u z / 2) (by linarith) z hz
  linarith

/-!
## The G3–G4 frontier (declared sorries, priced in the W9 lane plan)

Three statements remain open after G2: the Poisson-modification
capability and the off-pole harmonicity (G3, the latter conditional on
the W7-ii obligation), and the W6-germ corollary (G4).  All are
assemblies over landed surfaces.
-/

/--
**Uniform upper cap (G2, the §3.3 "bounded above with the right upper
profile").**  Every member is bounded by the truncated log cap plus a
single member-independent constant, on all of `V \ {p}` — the two-zone
§3.3 bound (`v ≤ -ℓ_p + C` on the disc, `v ≤ C'` off it) in one
formula.  With `V ⊆ ball p R₀`, the comparison gives
`v ≤ log R₀ - log ‖· - p‖`, i.e. the cap with `C = log R₀ - log ρ`.

The member-dependent pole constant washes out by a `θ → 0` device (no
annuli needed): for `θ > 0` the harmonic shift
`v + logCup p R₀ (-(1+θ))` is again a member of the comparison
subclass, and near the pole the extra `θ log ‖· - p‖ → -∞` swallows
the member's cap, so the eventual-boundary maximum principle applies
on all of `V \ {p}` at once; letting `θ → 0` leaves the
member-independent bound.  Downstream: `greensFamily_bddAbove`, the
profile upper half, and the W7 `hbdd` field.
-/
theorem greensFamily_le_truncatedLogCap_add {V : Set ℂ} {p : ℂ} {ρ : ℝ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hρ : 0 < ρ)
    (hsub : Metric.closedBall p ρ ⊆ V) :
    ∃ C : ℝ, ∀ v ∈ greensFamily V p, ∀ z ∈ V \ {p},
      v z ≤ truncatedLogCap p ρ z + C := by
  -- an outer radius R₀ > ρ with V ⊆ ball p R₀
  obtain ⟨R₁, hR₁⟩ := hVb.subset_ball p
  set R₀ : ℝ := max R₁ (ρ + 1) with hR₀def
  have hVR₀ : V ⊆ ball p R₀ := hR₁.trans (ball_subset_ball (le_max_left _ _))
  have hρR₀ : ρ < R₀ := lt_of_lt_of_le (lt_add_one ρ) (le_max_right _ _)
  have hp_in : p ∈ V := hsub (mem_closedBall_self hρ.le)
  have hWopen : IsOpen (V \ {p}) := hV.sdiff isClosed_singleton
  have hWb : Bornology.IsBounded (V \ {p}) := hVb.subset Set.diff_subset
  refine ⟨Real.log R₀ - Real.log ρ, ?_⟩
  rintro v ⟨hvS, hvF, Cv, hvC⟩ z hzVp
  -- the member-independent comparison, for every positive weight excess θ
  have hθbound : ∀ θ : ℝ, 0 < θ → ∀ w ∈ V \ {p},
      v w ≤ (1 + θ) * (Real.log R₀ - Real.log ‖w - p‖) := by
    intro θ hθpos
    set g : ℂ → ℝ := fun w => v w + logCup p R₀ (-(1 + θ)) w with hg
    have hgS : PerronSubOn g (V \ {p}) :=
      hvS.add_harmonicOnNhd
        ((logCup_harmonicOnNhd p R₀ (-(1 + θ))).mono fun w hw => hw.2)
    -- the eventual boundary trap for the shifted member
    have hgfr : ∀ ζ ∈ frontier (V \ {p}), ∀ ε : ℝ, 0 < ε →
        ∀ᶠ w in 𝓝[V \ {p}] ζ, g w ≤ ε := by
      rw [frontier_diff_singleton hV hp_in]
      rintro ζ (hζfr | hζp) ε hε
      · -- old frontier points: v's own trap; the shift is nonpositive on V \ {p}
        have hsh : ∀ w ∈ V \ {p}, logCup p R₀ (-(1 + θ)) w ≤ 0 := by
          intro w hw
          have hwpos : 0 < ‖w - p‖ := by
            simpa [norm_pos_iff] using sub_ne_zero.mpr (hw.2 : w ≠ p)
          have hwlt : ‖w - p‖ < R₀ := by
            rw [← dist_eq_norm]
            exact mem_ball.mp (hVR₀ hw.1)
          have hlog : Real.log ‖w - p‖ ≤ Real.log R₀ :=
            Real.log_le_log hwpos hwlt.le
          have hcup : logCup p R₀ (-(1 + θ)) w
              = -(1 + θ) * (Real.log R₀ - Real.log ‖w - p‖) := rfl
          rw [hcup]
          nlinarith
        filter_upwards [hvF ζ hζfr ε hε, eventually_mem_nhdsWithin]
          with w hw1 hw2
        have := hsh w hw2
        simp only [hg]
        linarith
      · -- the pole: the member cap plus θ·log ‖·-p‖ → -∞
        rw [Set.mem_singleton_iff] at hζp
        rw [hζp]
        have hmono : 𝓝[V \ {p}] p ≤ 𝓝[≠] p :=
          nhdsWithin_mono p fun w hw => hw.2
        have hev := eventually_le_logCup (c := p) (r := R₀) hθpos
          (θ * Real.log R₀ - (ε - Cv + (1 + θ) * Real.log R₀))
        filter_upwards [hvC.filter_mono hmono, hev.filter_mono hmono]
          with w hw1 hw2
        have hw2' : θ * Real.log R₀
            - (ε - Cv + (1 + θ) * Real.log R₀)
            ≤ θ * (Real.log R₀ - Real.log ‖w - p‖) := by
          simpa [logCup] using hw2
        have hexp : g w = (v w + Real.log ‖w - p‖)
            + θ * Real.log ‖w - p‖ - (1 + θ) * Real.log R₀ := by
          simp only [hg, logCup]
          ring
        rw [hexp]
        nlinarith
    -- the eventual-boundary maximum principle on the punctured domain
    have hg0 : ∀ w ∈ V \ {p}, g w ≤ 0 :=
      hgS.le_zero_of_eventually_frontier_le hWopen hWb hgfr
    intro w hw
    have h0 := hg0 w hw
    have hcup : logCup p R₀ (-(1 + θ)) w
        = -((1 + θ) * (Real.log R₀ - Real.log ‖w - p‖)) := by
      simp only [logCup]
      ring
    simp only [hg, hcup] at h0
    linarith
  -- θ → 0 at the fixed point z
  have hzpos : 0 < ‖z - p‖ := by
    simpa [norm_pos_iff] using sub_ne_zero.mpr (hzVp.2 : z ≠ p)
  have hzlt : ‖z - p‖ < R₀ := by
    rw [← dist_eq_norm]
    exact mem_ball.mp (hVR₀ hzVp.1)
  have hK : 0 ≤ Real.log R₀ - Real.log ‖z - p‖ :=
    sub_nonneg.mpr (Real.log_le_log hzpos hzlt.le)
  have hkey : v z - (Real.log R₀ - Real.log ‖z - p‖) ≤ 0 := by
    refine nonpos_of_forall_pos_mul_le hK fun θ hθpos => ?_
    have h := hθbound θ hθpos z hzVp
    nlinarith
  -- the cap dominates the comparison bound pointwise
  have h1 : Real.log ρ - Real.log ‖z - p‖ ≤ truncatedLogCap p ρ z := by
    rw [← logCup_one_apply p ρ z]
    exact le_max_left _ _
  linarith

/--
Pointwise boundedness of the family — the `hbdd` discharger for
`greensCandidate_nonneg`, `log_le_greensCandidate_add_log`, and the
W7 envelope hypotheses.  Assembly over the G2 cap.
-/
theorem greensFamily_bddAbove {V : Set ℂ} {p : ℂ} {ρ : ℝ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hρ : 0 < ρ)
    (hsub : Metric.closedBall p ρ ⊆ V) :
    ∀ z ∈ V \ {p}, BddAbove ((fun v => v z) '' greensFamily V p) := by
  obtain ⟨C, hC⟩ := greensFamily_le_truncatedLogCap_add hV hVb hρ hsub
  intro z hz
  refine ⟨truncatedLogCap p ρ z + C, ?_⟩
  rintro y ⟨v, hv, rfl⟩
  exact hC v hv z hz

/--
**Poisson-modification capability of the Green's family (G3).**  On any
comparison disc `closedBall c R ⊆ V \ {p}`, the M4 modification
`poissonSolution v c R` of a member is again a member dominating it:
membership's comparison clause is the landed `PerronSubOn.poissonModify`;
the boundary and pole clauses are inherited through the seam
(`poissonSolution` equals `v` off `ball c R`, and both the frontier of
`V` and the pole have neighborhoods missing the compact modification
disc); domination is `le_poissonSolution_of_mem_ball` inside, equality
outside.  Discharges the W7 `hmod` field for the off-pole harmonicity.
-/
theorem greensFamily_poissonModificationInput {V : Set ℂ} {p c : ℂ}
    {R : ℝ} (hV : IsOpen V) (hR : 0 < R)
    (hsub : Metric.closedBall c R ⊆ V \ {p}) :
    PoissonModificationInput (greensFamily V p) (V \ {p}) c R := by
  sorry

/--
**Two-sided pole profile (G2, §3.3).**  Near the pole,
`greensCandidate V p + log ‖· - p‖` is bounded in absolute value: the
lower half is `log_le_greensCandidate_add_log` (the explicit member),
the upper half follows from the uniform cap through
`perronEnvelope_le`.  This is the boundedness input of the W6 germ
corollary below.
-/
theorem greensCandidate_pole_profile {V : Set ℂ} {p : ℂ} {ρ : ℝ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hρ : 0 < ρ)
    (hsub : Metric.closedBall p ρ ⊆ V) :
    ∃ C : ℝ, ∀ᶠ z in 𝓝[≠] p,
      |greensCandidate V p z + Real.log ‖z - p‖| ≤ C := by
  obtain ⟨C, hC⟩ := greensFamily_le_truncatedLogCap_add hV hVb hρ hsub
  have hbdd := greensFamily_bddAbove hV hVb hρ hsub
  refine ⟨max (Real.log ρ + C) (-Real.log ρ), ?_⟩
  have hball : ∀ᶠ z in 𝓝 p, z ∈ ball p ρ :=
    isOpen_ball.eventually_mem (mem_ball_self hρ)
  filter_upwards [log_le_greensCandidate_add_log hV hρ hsub hbdd,
    hball.filter_mono nhdsWithin_le_nhds, eventually_mem_nhdsWithin]
    with z hlow hzball hzne
  have hzp : z ≠ p := hzne
  have hzV : z ∈ V \ {p} := ⟨hsub (ball_subset_closedBall hzball), hzp⟩
  have hzρ : ‖z - p‖ ≤ ρ := by
    rw [← dist_eq_norm]
    exact (Metric.mem_ball.mp hzball).le
  have hcup : 0 ≤ logCup p ρ 1 z := logCup_nonneg one_pos.le hzp hzρ
  have hcap : truncatedLogCap p ρ z = Real.log ρ - Real.log ‖z - p‖ := by
    show max (logCup p ρ 1 z) 0 = _
    rw [max_eq_left hcup, logCup_one_apply]
  -- the upper half: every member is below the cap, so the envelope is
  have hup : greensCandidate V p z
      ≤ Real.log ρ - Real.log ‖z - p‖ + C :=
    perronEnvelope_le greensFamily_nonempty fun v hv =>
      (hC v hv z hzV).trans_eq (by rw [hcap])
  rw [abs_le]
  constructor
  · have h2 : -Real.log ρ ≤ max (Real.log ρ + C) (-Real.log ρ) :=
      le_max_right _ _
    linarith
  · have h2 : Real.log ρ + C ≤ max (Real.log ρ + C) (-Real.log ρ) :=
      le_max_left _ _
    linarith

/--
**Off-pole harmonicity (G3, §3.3 "harmonic" via Perron's lemma).**  The
candidate is harmonic on the punctured domain, conditionally on the
W7-ii obligation: at each `z ∈ V \ {p}` pick a comparison disc inside
the punctured domain and apply `PerronEnvelopeHarmonicInput` to the
family — nonemptiness (`zero_mem_greensFamily`), max-closure
(`greensFamily_max_mem`), pointwise bounds (`greensFamily_bddAbove`),
and the modification capability
(`greensFamily_poissonModificationInput`) supply its fields.
-/
theorem greensCandidate_harmonicOnNhd_off_pole
    (hW7 : PerronEnvelopeHarmonicInput) {V : Set ℂ} {p : ℂ} {ρ : ℝ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hρ : 0 < ρ)
    (hsub : Metric.closedBall p ρ ⊆ V) :
    HarmonicOnNhd (greensCandidate V p) (V \ {p}) := by
  sorry

/--
**W6-germ corollary (G4, §3.3 "pole germ").**  The shifted candidate
`greensCandidate V p + log ‖· - p‖` has a limit at the pole: it is
harmonic on a punctured disc (off-pole harmonicity plus
`harmonicAt_log_norm_sub`) and bounded there (the two-sided profile),
so jc9's removable-singularity surface
(`exists_tendsto_of_bounded_punctured`, with the discharged W1/W3
inputs) extends it across `p`.  This is the exact germ datum the W10
stage assembly consumes at `P0`/`Pinf` (`𝓝[≠] p` agrees with the
surface's punctured-ball filter near `p`).
-/
theorem greensCandidate_add_log_tendsto
    (hW7 : PerronEnvelopeHarmonicInput) {V : Set ℂ} {p : ℂ} {ρ : ℝ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hρ : 0 < ρ)
    (hsub : Metric.closedBall p ρ ⊆ V) :
    ∃ L : ℝ, Tendsto (fun z => greensCandidate V p z + Real.log ‖z - p‖)
      (𝓝[≠] p) (𝓝 L) := by
  sorry

end JacobianChallenge.HolomorphicForms
