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
through the frozen `perronEnvelope`, and the named frontier statements —
the uniform upper cap, the Poisson-modification capability, the
two-sided pole profile, the off-pole harmonicity, and the W6-germ
corollary — as declared `sorry`s priced into slices G2–G4.

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
## The G2–G4 frontier (declared sorries, priced in the W9 lane plan)

Five statements, in dependency order.  The single genuinely hard one is
the uniform upper cap (G2): the §3.3 punctured-disc comparison, where
the member-dependent pole constant washes out (compare on
`V \ closedBall p δ` against
`ε + (C_v - log δ)·(log R₀ - log ‖·-p‖)/log (R₀/δ)` and let `δ → 0`);
it needs an eventual-boundary variant of the weak maximum principle
(members are not continuous up to `closure V`), built locally from the
landed W1 on shrunk domains.  The rest are assemblies over landed
surfaces.
-/

/--
**Uniform upper cap (G2, the §3.3 "bounded above with the right upper
profile").**  Every member is bounded by the truncated log cap plus a
single member-independent constant, on all of `V \ {p}` — the two-zone
§3.3 bound (`v ≤ -ℓ_p + C` on the disc, `v ≤ C'` off it) in one
formula.  With `V ⊆ ball p R₀`, the classical comparison gives
`v ≤ log R₀ - log ‖· - p‖`, i.e. the cap with `C = log (R₀/ρ)`.
Downstream: `greensFamily_bddAbove`, the profile upper half, and the
W7 `hbdd` field.
-/
theorem greensFamily_le_truncatedLogCap_add {V : Set ℂ} {p : ℂ} {ρ : ℝ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hρ : 0 < ρ)
    (hsub : Metric.closedBall p ρ ⊆ V) :
    ∃ C : ℝ, ∀ v ∈ greensFamily V p, ∀ z ∈ V \ {p},
      v z ≤ truncatedLogCap p ρ z + C := by
  sorry

/--
Pointwise boundedness of the family — the `hbdd` discharger for
`greensCandidate_nonneg`, `log_le_greensCandidate_add_log`, and the
W7 envelope hypotheses.  Direct-sorry-free assembly over the G2 cap
(probes `sorryAx` through `greensFamily_le_truncatedLogCap_add` until
G2 lands).
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
  sorry

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
