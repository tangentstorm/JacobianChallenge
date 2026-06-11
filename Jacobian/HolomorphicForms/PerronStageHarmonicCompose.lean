import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Jacobian.HolomorphicForms.HarmonicConjugate

/-!
# Harmonicity composes with analytic maps (B2 toolbox W2)

Blueprint node: `lem:stage-harmonic-analytic-compose`.

B2 Dirichlet toolbox leaf W2 (`docs/perron-b2-dirichlet-phase0.md`):
precomposing a harmonic function with an analytic map preserves
harmonicity.  This is the chart-transfer workhorse for the Perron stage
construction — stage potentials move between source charts through
analytic transitions, and B3 compact bounds / B4 conjugate transfer / the
W5 `PerronSubOn` API all consume exactly this.

Route: localize `HarmonicAt` to a ball (`isOpen_setOf_harmonicAt`),
represent the potential there as the real part of an analytic `F`
(`InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq`),
compose (`AnalyticAt.comp`), take real parts
(`AnalyticAt.harmonicAt_re`), and transfer back along the eventual
equality `u ∘ f =ᶠ (re ∘ F) ∘ f` (`harmonicAt_congr_nhds`).
-/

namespace JacobianChallenge.HolomorphicForms

open InnerProductSpace Metric Set

/--
**B2 toolbox W2.** Precomposition with an analytic map preserves
harmonicity at a point: if `u` is harmonic at `f z₀` and `f` is
ℂ-analytic at `z₀`, then `u ∘ f` is harmonic at `z₀`.
-/
theorem HarmonicAt.comp_analyticAt
    {u : ℂ → ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (hu : HarmonicAt u (f z₀)) (hf : AnalyticAt ℂ f z₀) :
    HarmonicAt (u ∘ f) z₀ := by
  obtain ⟨R, hR, hball⟩ :=
    Metric.isOpen_iff.mp (isOpen_setOf_harmonicAt u) (f z₀) hu
  have huOn : HarmonicOnNhd u (Metric.ball (f z₀) R) := fun x hx => hball hx
  obtain ⟨F, hF_an, hF_eq⟩ := huOn.exists_analyticOnNhd_ball_re_eq
  have hFf_an : AnalyticAt ℂ (F ∘ f) z₀ :=
    (hF_an (f z₀) (Metric.mem_ball_self hR)).comp hf
  have hre : HarmonicAt (fun z => ((F ∘ f) z).re) z₀ := hFf_an.harmonicAt_re
  have hev : (fun z => ((F ∘ f) z).re) =ᶠ[nhds z₀] (u ∘ f) := by
    have hmem : f ⁻¹' Metric.ball (f z₀) R ∈ nhds z₀ :=
      hf.continuousAt.preimage_mem_nhds
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR))
    filter_upwards [hmem] with z hz
    exact hF_eq hz
  exact (harmonicAt_congr_nhds hev).mp hre

/--
On-set version: if `u` is harmonic on a neighborhood of `V`, `f` is
analytic on `U`, and `f` maps `U` into `V`, then `u ∘ f` is harmonic on a
neighborhood of `U`.
-/
theorem HarmonicOnNhd.comp_analyticOnNhd
    {u : ℂ → ℝ} {f : ℂ → ℂ} {U V : Set ℂ}
    (hu : HarmonicOnNhd u V) (hf : AnalyticOnNhd ℂ f U)
    (hUV : Set.MapsTo f U V) :
    HarmonicOnNhd (u ∘ f) U :=
  fun z hz => HarmonicAt.comp_analyticAt (hu (f z) (hUV hz)) (hf z hz)

/--
Chart-transition corollary — the W5/B4 chart-transfer shape: a potential
harmonic at the image of a point under the chart transition
`chartAt ℂ P ∘ (chartAt ℂ x).symm` pulls back to a potential harmonic at
that point, for any `w` in the transition overlap.  The transition is
analytic there by `chart_transition_contDiffOn`.
-/
theorem HarmonicAt.comp_chart_transition
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (x P : X) {u : ℂ → ℝ} {w : ℂ}
    (hw : w ∈ (chartAt ℂ x).target ∩
      (chartAt ℂ x).symm ⁻¹' (chartAt ℂ P).source)
    (hu : HarmonicAt u (chartAt ℂ P ((chartAt ℂ x).symm w))) :
    HarmonicAt (u ∘ (chartAt ℂ P ∘ (chartAt ℂ x).symm)) w := by
  have hopen : IsOpen ((chartAt ℂ x).target ∩
      (chartAt ℂ x).symm ⁻¹' (chartAt ℂ P).source) :=
    (chartAt ℂ x).continuousOn_symm.isOpen_inter_preimage
      (chartAt ℂ x).open_target (chartAt ℂ P).open_source
  have htrans_an : AnalyticAt ℂ (chartAt ℂ P ∘ (chartAt ℂ x).symm) w :=
    AnalyticOn.analyticAt (hopen.mem_nhds hw)
      (chart_transition_contDiffOn x P).analyticOn
  exact HarmonicAt.comp_analyticAt hu htrans_an

end JacobianChallenge.HolomorphicForms
