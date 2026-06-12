import Jacobian.HolomorphicForms.PerronSubOn
import Jacobian.HolomorphicForms.PerronHarnackLimit

/-!
# Perron envelope: definition and the center-touch core (B2 toolbox W7-i)

Blueprint node: `lem:perron-envelope-center-touch`.

The Perron construction (pricing doc §3.3) produces harmonic functions
as pointwise suprema of families of comparison subfunctions.  This file
opens the W7 lane (claims board c756945d): it defines the envelope,
freezes the *Poisson modification* obligation — the W5b/W3d-gated
capability of replacing a family member by a dominating member harmonic
on a given disc — and proves the half of Perron's lemma that is green
today: through every point of the disc there is a harmonic function
below the envelope and touching it at that point.

The construction is the §3.3 textbook one: approximate the envelope at
`x₀` by members, monotonize with `max` (W5a closure), modify into
disc-harmonic members (the frozen oracle), and pass to the limit with
the W4 Harnack convergence corollary (`PerronHarnackLimit.lean`).

What is deliberately NOT here (W7-ii/iii, per the approved series): the
second-comparison step identifying the touching function with the
envelope *throughout* the disc (needs a strong maximum principle on
balls, dischargeable from W4a's Harnack with no W1 dependency) and the
chart-covered-`X` locality packaging.
-/

namespace JacobianChallenge.HolomorphicForms

open Complex InnerProductSpace Metric Real Filter Topology

/-!
## The envelope and its basic API
-/

/--
The **Perron envelope** of a family `F` of real functions on `ℂ`: the
pointwise supremum.  Junk (`sSup ∅ = 0`) where the family is empty or
unbounded; the API lemmas carry the nonemptiness/boundedness side
conditions.
-/
noncomputable def perronEnvelope (F : Set (ℂ → ℝ)) : ℂ → ℝ :=
  fun z => sSup ((fun v => v z) '' F)

/-- Members lie below the envelope wherever the family is bounded. -/
theorem le_perronEnvelope {F : Set (ℂ → ℝ)} {v : ℂ → ℝ} (hv : v ∈ F)
    {z : ℂ} (hbdd : BddAbove ((fun v => v z) '' F)) :
    v z ≤ perronEnvelope F z :=
  le_csSup hbdd ⟨v, hv, rfl⟩

/-- The envelope lies below any pointwise upper bound of the family. -/
theorem perronEnvelope_le {F : Set (ℂ → ℝ)} {z : ℂ} {M : ℝ}
    (hne : F.Nonempty) (hM : ∀ v ∈ F, v z ≤ M) :
    perronEnvelope F z ≤ M :=
  csSup_le (hne.image _) (by rintro y ⟨v, hv, rfl⟩; exact hM v hv)

/-- Approximation: any value below the envelope is beaten by a member. -/
theorem exists_lt_of_lt_perronEnvelope {F : Set (ℂ → ℝ)} {z : ℂ} {y : ℝ}
    (hne : F.Nonempty) (hy : y < perronEnvelope F z) :
    ∃ v ∈ F, y < v z := by
  obtain ⟨_, ⟨v, hv, rfl⟩, h⟩ := exists_lt_of_lt_csSup (hne.image _) hy
  exact ⟨v, hv, h⟩

/-!
## The frozen modification obligation
-/

/--
**Poisson modification obligation (frozen interface, W5b/W3d lane).**
Every member of the family can be replaced by a member that dominates
it on `V` and is harmonic on the disc `ball c R`.  In the Perron
construction this is the harmonic replacement `P[v|∂D]` inside the disc
(`v` outside), whose membership and seam continuity are the gated W3d
boundary-attainment work; W7 consumes the capability through this named
`Prop`, following the `WeakMaxPrincipleInput` convention
(`PerronRemovableSingularity.lean`).
-/
def PoissonModificationInput (F : Set (ℂ → ℝ)) (V : Set ℂ) (c : ℂ)
    (R : ℝ) : Prop :=
  ∀ v ∈ F, ∃ v', v' ∈ F ∧ (∀ z ∈ V, v z ≤ v' z) ∧
    HarmonicOnNhd v' (ball c R)

/-!
## Harnack convergence on open balls

`harnack_increasing_limit_harmonic` (`PerronHarnackLimit.lean`) is
stated for families harmonic on a neighborhood of a *closed* ball; the
modification oracle produces functions harmonic on the *open* ball
only.  The open-ball version follows by shrinking: the pointwise-sup
limit does not depend on the radius, so the local limits glue.
-/

/--
**Harnack convergence corollary, open-ball version.**  An increasing
sequence of harmonic functions on `ball c R`, bounded at the center,
converges pointwise on the ball to a harmonic function.
-/
theorem harnack_increasing_limit_harmonic_ball {h : ℕ → ℂ → ℝ} {c : ℂ}
    {R : ℝ} (hR : 0 < R)
    (hh : ∀ n, HarmonicOnNhd (h n) (ball c R))
    (hmono : ∀ z ∈ ball c R, Monotone fun n => h n z)
    (hbdd : BddAbove (Set.range fun n => h n c)) :
    ∃ H : ℂ → ℝ,
      (∀ z ∈ ball c R, Tendsto (fun n => h n z) atTop (𝓝 (H z))) ∧
      HarmonicOnNhd H (ball c R) := by
  -- per-point data on a strictly smaller closed ball
  have key : ∀ z ∈ ball c R, ∃ R' : ℝ, 0 < R' ∧ R' < R ∧ z ∈ ball c R' ∧
      closedBall c R' ⊆ ball c R := by
    intro z hz
    have hz' : ‖z - c‖ < R := mem_ball_iff_norm.mp hz
    have h0 : 0 ≤ ‖z - c‖ := norm_nonneg _
    refine ⟨(‖z - c‖ + R) / 2, by linarith, by linarith,
      mem_ball_iff_norm.mpr (by linarith), fun w hw => ?_⟩
    rw [mem_ball_iff_norm]
    have := mem_closedBall_iff_norm.mp hw
    linarith
  -- pointwise convergence to the supremum
  have hpt : ∀ z ∈ ball c R,
      Tendsto (fun n => h n z) atTop (𝓝 (⨆ n, h n z)) := by
    intro z hz
    obtain ⟨R', hR'0, hR'R, hzR', hsub⟩ := key z hz
    obtain ⟨H', h1, -, -⟩ := harnack_increasing_limit_harmonic
      (fun n => (hh n).mono hsub) (fun w hw => hmono w (hsub hw)) hbdd
    have ht := h1 z hzR'
    have hmz : Monotone fun n => h n z := hmono z hz
    have hub : ∀ n, h n z ≤ H' z := fun n =>
      ge_of_tendsto ht (eventually_atTop.mpr ⟨n, fun m hm => hmz hm⟩)
    exact tendsto_atTop_ciSup hmz ⟨H' z, by rintro x ⟨n, rfl⟩; exact hub n⟩
  -- harmonicity of the supremum
  refine ⟨fun z => ⨆ n, h n z, hpt, fun z hz => ?_⟩
  obtain ⟨R', hR'0, hR'R, hzR', hsub⟩ := key z hz
  obtain ⟨H', h1, -, h3⟩ := harnack_increasing_limit_harmonic
    (fun n => (hh n).mono hsub) (fun w hw => hmono w (hsub hw)) hbdd
  have heq : (fun w => ⨆ n, h n w) =ᶠ[𝓝 z] H' := by
    filter_upwards [isOpen_ball.mem_nhds hzR'] with w hw
    exact tendsto_nhds_unique
      (hpt w (ball_subset_ball hR'R.le hw)) (h1 w hw)
  exact (harmonicAt_congr_nhds heq).mpr (h3 z hzR')

/-!
## The center-touch core of Perron's lemma (W7-i)
-/

/--
**Perron's lemma, center-touch core.**  For a nonempty family `F`,
closed under pointwise `max` and pointwise bounded above on `V`, with
the Poisson modification capability on a disc `closedBall c R ⊆ V`:
through every point `x₀` of the open disc there is a function harmonic
on the disc, lying below the envelope, and *equal* to the envelope at
`x₀`.  (That the envelope itself is harmonic — equality throughout —
is the W7-ii second-comparison step.)
-/
theorem perronEnvelope_exists_harmonic_eq_at {F : Set (ℂ → ℝ)}
    {V : Set ℂ} {c : ℂ} {R : ℝ}
    (hne : F.Nonempty)
    (hmax : ∀ v₁ ∈ F, ∀ v₂ ∈ F, (fun z => max (v₁ z) (v₂ z)) ∈ F)
    (hbdd : ∀ z ∈ V, BddAbove ((fun v => v z) '' F))
    (hR : 0 < R) (hball : closedBall c R ⊆ V)
    (hmod : PoissonModificationInput F V c R)
    {x₀ : ℂ} (hx₀ : x₀ ∈ ball c R) :
    ∃ H : ℂ → ℝ, HarmonicOnNhd H (ball c R) ∧
      (∀ z ∈ ball c R, H z ≤ perronEnvelope F z) ∧
      H x₀ = perronEnvelope F x₀ := by
  have hx₀V : x₀ ∈ V := hball (ball_subset_closedBall hx₀)
  have hcV : c ∈ V := hball (mem_closedBall_self hR.le)
  have hballV : ∀ z ∈ ball c R, z ∈ V :=
    fun z hz => hball (ball_subset_closedBall hz)
  -- approximating members at x₀
  have happrox : ∀ n : ℕ, ∃ v ∈ F,
      perronEnvelope F x₀ - 1 / (n + 1) < v x₀ := by
    intro n
    apply exists_lt_of_lt_perronEnvelope hne
    have : (0 : ℝ) < 1 / (n + 1) := by positivity
    linarith
  choose v hvF hvx using happrox
  -- the modification oracle, as functions
  choose mod hmodF hmodLe hmodHarm using hmod
  -- the interleaved max/modify sequence, carrying membership
  let g : ℕ → {w : ℂ → ℝ // w ∈ F} := fun n =>
    Nat.rec (motive := fun _ => {w : ℂ → ℝ // w ∈ F})
      ⟨mod (v 0) (hvF 0), hmodF _ _⟩
      (fun k ih => ⟨mod (fun z => max (v (k + 1) z) (ih.1 z))
        (hmax _ (hvF (k + 1)) _ ih.2), hmodF _ _⟩) n
  -- each term is harmonic on the disc
  have hgHarm : ∀ n, HarmonicOnNhd (g n).1 (ball c R) := by
    intro n
    cases n with
    | zero => exact hmodHarm _ _
    | succ k => exact hmodHarm _ _
  -- each term dominates its approximant on V
  have hgv : ∀ n, ∀ z ∈ V, v n z ≤ (g n).1 z := by
    intro n z hz
    cases n with
    | zero => exact hmodLe (v 0) (hvF 0) z hz
    | succ k =>
        exact le_trans (le_max_left _ _)
          (hmodLe _ (hmax _ (hvF (k + 1)) _ (g k).2) z hz)
  -- the sequence increases on V
  have hgstep : ∀ n, ∀ z ∈ V, (g n).1 z ≤ (g (n + 1)).1 z := by
    intro n z hz
    exact le_trans (le_max_right _ _)
      (hmodLe _ (hmax _ (hvF (n + 1)) _ (g n).2) z hz)
  have hgmono : ∀ z ∈ V, Monotone fun n => (g n).1 z :=
    fun z hz => monotone_nat_of_le_succ fun n => hgstep n z hz
  -- members stay below the envelope
  have hgle : ∀ n, ∀ z ∈ V, (g n).1 z ≤ perronEnvelope F z :=
    fun n z hz => le_perronEnvelope (g n).2 (hbdd z hz)
  -- pass to the limit (W4, open-ball version)
  obtain ⟨H, hHpt, hHharm⟩ := harnack_increasing_limit_harmonic_ball hR
    hgHarm (fun z hz => hgmono z (hballV z hz))
    ⟨perronEnvelope F c, by rintro x ⟨n, rfl⟩; exact hgle n c hcV⟩
  refine ⟨H, hHharm, ?_, ?_⟩
  -- the limit lies below the envelope
  · intro z hz
    exact le_of_tendsto (hHpt z hz)
      (Eventually.of_forall fun n => hgle n z (hballV z hz))
  -- the limit touches the envelope at x₀
  · have hle : H x₀ ≤ perronEnvelope F x₀ :=
      le_of_tendsto (hHpt x₀ hx₀)
        (Eventually.of_forall fun n => hgle n x₀ hx₀V)
    have hge : perronEnvelope F x₀ ≤ H x₀ := by
      -- each truncated lower bound survives the limit
      have h1 : ∀ n : ℕ, perronEnvelope F x₀ - 1 / (n + 1) ≤ H x₀ := by
        intro n
        apply ge_of_tendsto (hHpt x₀ hx₀)
        filter_upwards [eventually_ge_atTop n] with k hk
        calc perronEnvelope F x₀ - 1 / (n + 1)
            ≤ v n x₀ := (hvx n).le
          _ ≤ (g n).1 x₀ := hgv n x₀ hx₀V
          _ ≤ (g k).1 x₀ := hgmono x₀ hx₀V hk
      -- and the truncations converge to the envelope value
      have h2 : Tendsto (fun n : ℕ => perronEnvelope F x₀ - 1 / (n + 1))
          atTop (𝓝 (perronEnvelope F x₀)) := by
        simpa using Filter.Tendsto.const_sub (perronEnvelope F x₀)
          tendsto_one_div_add_atTop_nhds_zero_nat
      exact le_of_tendsto h2 (Eventually.of_forall h1)
    exact le_antisymm hle hge

/-!
## The second comparison: the envelope is harmonic (W7-ii)

The center-touch core produces, at each point, a harmonic minorant
touching the envelope there.  The second diagonal upgrades the touch
to equality throughout the disc: a second modified sequence, seeded by
the first one and by approximants at an arbitrary `y`, has a harmonic
limit `K` dominating the first limit `H`, agreeing with it at the
center, and touching the envelope at `y`; interior-touch rigidity
(`eq_on_ball_of_harmonic_le_of_eq_at`, W7-iii) forces `H = K`, so the
envelope agrees with the single harmonic `H` everywhere on the disc.
-/

/--
The interleaved max/modify pass, factored over an arbitrary input
sequence `a` of members: produce a sequence of members harmonic on the
modification disc, increasing on `V`, and dominating `a` termwise.
-/
private lemma exists_modified_seq {F : Set (ℂ → ℝ)} {V : Set ℂ}
    {c : ℂ} {R : ℝ}
    (hmax : ∀ v₁ ∈ F, ∀ v₂ ∈ F, (fun z => max (v₁ z) (v₂ z)) ∈ F)
    (hmod : PoissonModificationInput F V c R)
    (a : ℕ → ℂ → ℝ) (haF : ∀ n, a n ∈ F) :
    ∃ g : ℕ → ℂ → ℝ, (∀ n, g n ∈ F) ∧
      (∀ n, HarmonicOnNhd (g n) (ball c R)) ∧
      (∀ z ∈ V, Monotone fun n => g n z) ∧
      (∀ n, ∀ z ∈ V, a n z ≤ g n z) := by
  choose mod hmodF hmodLe hmodHarm using hmod
  let g : ℕ → {w : ℂ → ℝ // w ∈ F} := fun n =>
    Nat.rec (motive := fun _ => {w : ℂ → ℝ // w ∈ F})
      ⟨mod (a 0) (haF 0), hmodF _ _⟩
      (fun k ih => ⟨mod (fun z => max (a (k + 1) z) (ih.1 z))
        (hmax _ (haF (k + 1)) _ ih.2), hmodF _ _⟩) n
  refine ⟨fun n => (g n).1, fun n => (g n).2, ?_, ?_, ?_⟩
  · intro n
    cases n with
    | zero => exact hmodHarm _ _
    | succ k => exact hmodHarm _ _
  · intro z hz
    apply monotone_nat_of_le_succ
    intro n
    exact le_trans (le_max_right _ _)
      (hmodLe _ (hmax _ (haF (n + 1)) _ (g n).2) z hz)
  · intro n z hz
    cases n with
    | zero => exact hmodLe (a 0) (haF 0) z hz
    | succ k =>
        exact le_trans (le_max_left _ _)
          (hmodLe _ (hmax _ (haF (k + 1)) _ (g k).2) z hz)

/--
**Perron's lemma** (W7-ii, the planar envelope lemma; pricing doc
§3.3): for a nonempty family closed under pointwise `max`, pointwise
bounded above on `V`, with the Poisson modification capability on a
disc `closedBall c R ⊆ V`, the Perron envelope is harmonic on the open
disc.  This is the exact shape frozen as
`PerronEnvelopeHarmonicInput` by the W9 consumer
(`PerronGreensFunction.lean`); no `PerronSubOn` hypothesis is needed.
-/
theorem perronEnvelope_harmonicOnNhd_ball {F : Set (ℂ → ℝ)}
    {V : Set ℂ} {c : ℂ} {R : ℝ}
    (hne : F.Nonempty)
    (hmax : ∀ v₁ ∈ F, ∀ v₂ ∈ F, (fun z => max (v₁ z) (v₂ z)) ∈ F)
    (hbdd : ∀ z ∈ V, BddAbove ((fun v => v z) '' F))
    (hR : 0 < R) (hball : closedBall c R ⊆ V)
    (hmod : PoissonModificationInput F V c R) :
    HarmonicOnNhd (perronEnvelope F) (ball c R) := by
  set u := perronEnvelope F with hu
  have hcV : c ∈ V := hball (mem_closedBall_self hR.le)
  have hballV : ∀ z ∈ ball c R, z ∈ V :=
    fun z hz => hball (ball_subset_closedBall hz)
  have hcball : c ∈ ball c R := mem_ball_self hR
  -- first sequence: approximants at the center, modified
  have happx : ∀ n : ℕ, ∃ v ∈ F, u c - 1 / (n + 1) < v c := by
    intro n
    apply exists_lt_of_lt_perronEnvelope hne
    have : (0 : ℝ) < 1 / (n + 1) := by positivity
    linarith
  choose v hvF hvc using happx
  obtain ⟨g, hgF, hgHarm, hgmono, hgdom⟩ := exists_modified_seq hmax hmod v hvF
  have hgle : ∀ n, ∀ z ∈ V, g n z ≤ u z :=
    fun n z hz => le_perronEnvelope (hgF n) (hbdd z hz)
  obtain ⟨H, hHpt, hHharm⟩ := harnack_increasing_limit_harmonic_ball hR hgHarm
    (fun z hz => hgmono z (hballV z hz))
    ⟨u c, by rintro x ⟨n, rfl⟩; exact hgle n c hcV⟩
  have hHle : ∀ z ∈ ball c R, H z ≤ u z := fun z hz =>
    le_of_tendsto (hHpt z hz)
      (Eventually.of_forall fun n => hgle n z (hballV z hz))
  -- the first limit touches the envelope at the center
  have hHc : H c = u c := by
    refine le_antisymm (hHle c hcball) ?_
    have h1 : ∀ n : ℕ, u c - 1 / (n + 1) ≤ H c := by
      intro n
      apply ge_of_tendsto (hHpt c hcball)
      filter_upwards [eventually_ge_atTop n] with m hm
      calc u c - 1 / (n + 1)
          ≤ v n c := (hvc n).le
        _ ≤ g n c := hgdom n c hcV
        _ ≤ g m c := hgmono c hcV hm
    have h2 : Tendsto (fun n : ℕ => u c - 1 / (n + 1)) atTop (𝓝 (u c)) := by
      simpa using Filter.Tendsto.const_sub (u c)
        tendsto_one_div_add_atTop_nhds_zero_nat
    exact le_of_tendsto h2 (Eventually.of_forall h1)
  -- second diagonal: the envelope agrees with `H` everywhere
  have hkey : ∀ y ∈ ball c R, u y = H y := by
    intro y hy
    have hyV : y ∈ V := hballV y hy
    have happy : ∀ n : ℕ, ∃ w ∈ F, u y - 1 / (n + 1) < w y := by
      intro n
      apply exists_lt_of_lt_perronEnvelope hne
      have : (0 : ℝ) < 1 / (n + 1) := by positivity
      linarith
    choose b hbF hby using happy
    obtain ⟨k, hkF, hkHarm, hkmono, hkdom⟩ := exists_modified_seq hmax hmod
      (fun n z => max (b n z) (g n z))
      (fun n => hmax _ (hbF n) _ (hgF n))
    have hkle : ∀ n, ∀ z ∈ V, k n z ≤ u z :=
      fun n z hz => le_perronEnvelope (hkF n) (hbdd z hz)
    obtain ⟨K, hKpt, hKharm⟩ := harnack_increasing_limit_harmonic_ball hR
      hkHarm (fun z hz => hkmono z (hballV z hz))
      ⟨u c, by rintro x ⟨n, rfl⟩; exact hkle n c hcV⟩
    have hKle : ∀ z ∈ ball c R, K z ≤ u z := fun z hz =>
      le_of_tendsto (hKpt z hz)
        (Eventually.of_forall fun n => hkle n z (hballV z hz))
    -- the second sequence dominates the first
    have hHK : ∀ z ∈ ball c R, H z ≤ K z := by
      intro z hz
      apply le_of_tendsto_of_tendsto (hHpt z hz) (hKpt z hz)
      filter_upwards with n
      exact le_trans (le_max_right _ _) (hkdom n z (hballV z hz))
    -- equality at the center
    have hKc : H c = K c :=
      le_antisymm (hHK c hcball) (by rw [hHc]; exact hKle c hcball)
    -- the second limit touches the envelope at `y`
    have hKy : K y = u y := by
      refine le_antisymm (hKle y hy) ?_
      have h1 : ∀ n : ℕ, u y - 1 / (n + 1) ≤ K y := by
        intro n
        apply ge_of_tendsto (hKpt y hy)
        filter_upwards [eventually_ge_atTop n] with m hm
        calc u y - 1 / (n + 1)
            ≤ b n y := (hby n).le
          _ ≤ max (b n y) (g n y) := le_max_left _ _
          _ ≤ k n y := hkdom n y hyV
          _ ≤ k m y := hkmono y hyV hm
      have h2 : Tendsto (fun n : ℕ => u y - 1 / (n + 1)) atTop (𝓝 (u y)) := by
        simpa using Filter.Tendsto.const_sub (u y)
          tendsto_one_div_add_atTop_nhds_zero_nat
      exact le_of_tendsto h2 (Eventually.of_forall h1)
    -- interior-touch rigidity collapses the diagonal
    have heq := eq_on_ball_of_harmonic_le_of_eq_at hHharm hKharm hHK
      hcball hKc
    calc u y = K y := hKy.symm
      _ = H y := (heq y hy).symm
  -- transfer harmonicity along the germ equality
  intro z hz
  have heqv : H =ᶠ[𝓝 z] u := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact (hkey w hw).symm
  exact (harmonicAt_congr_nhds heqv).mp (hHharm z hz)

end JacobianChallenge.HolomorphicForms


