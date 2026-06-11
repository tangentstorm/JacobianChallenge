import Mathlib.Analysis.Complex.Harmonic.Analytic
import Jacobian.HolomorphicForms.StageDirichlet
import Jacobian.HolomorphicForms.PerronConjugateUniqueness

/-!
# Bridge: chartwise harmonicity to neighborhood-uniform conjugates

B4 work item W2 (`docs/perron-b4-conjugate-phase0.md`), the "§3.8 routine
bridge" of `docs/perron-b2-dirichlet-phase0.md`: B2's chartwise
`InnerProductSpace.HarmonicOnNhd` export (`StageHarmonicOnNhd`, the landed
R2 shape) implies the neighborhood-uniform conjugate form
(`StageHarmonicOn`).  The conjugate witness is the imaginary part of the
analytic completion produced by
`InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq`, read
back through the chart.

This is the fiber-nonemptiness input for the W3/W4 conjugate-germ covering
space.
-/

namespace JacobianChallenge.HolomorphicForms

open Metric

/-- The W2 bridge: chartwise neighborhood harmonicity
(`StageHarmonicOnNhd`, B2's export shape) implies neighborhood-uniform
local conjugates (`StageHarmonicOn`).

At `x ∈ stage` off the marked points, the hypothesis provides a chart ball
`B` (inside the chart target, with `symm '' B ⊆ stage`) on which the chart
reading of the potential is harmonic;
`InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq` produces
an analytic `F` on `B` with `Re ∘ F` equal to that reading, the conjugate
candidate is `v := fun q => (F (chartAt ℂ x q)).im`, the pullback pair
agrees with `F` on `B` (so it is ℂ-level conjugate at every point of `B`),
and `IsHarmonicConjugateAtReal.of_transfer_chart` lands the `X`-level
predicate at every point of the open set
`(chartAt ℂ x).source ∩ chartAt ℂ x ⁻¹' B ⊆ stage`. -/
theorem StageHarmonicOnNhd.stageHarmonicOn
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    {e : X ≃ₜ OnePoint ℂ} {marked : GenusZeroStageMarkedData X e}
    {stage : Set X} {potential : X → ℝ}
    (h : StageHarmonicOnNhd X marked stage potential) :
    StageHarmonicOn X marked stage potential := by
  intro x hx hP0 hPinf
  obtain ⟨r, hr0, hball_t, himg, hharm⟩ := h x hx hP0 hPinf
  set z₀ : ℂ := (chartAt ℂ x) x with hz₀
  obtain ⟨F, hF_an, hF_eq⟩ :=
    InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq hharm
  -- The open neighborhood of `x` carrying the uniform conjugate.
  refine ⟨(chartAt ℂ x).source ∩ chartAt ℂ x ⁻¹' ball z₀ r,
    (chartAt ℂ x).continuousOn.isOpen_inter_preimage
      (chartAt ℂ x).open_source isOpen_ball,
    ⟨mem_chart_source ℂ x, by
      rw [Set.mem_preimage, ← hz₀]
      exact mem_ball_self hr0⟩,
    ?_, fun q => (F (chartAt ℂ x q)).im, fun y hy => ?_⟩
  · -- The neighborhood sits inside the stage via the symm-image field.
    intro q hq
    have hq_inv : (chartAt ℂ x).symm ((chartAt ℂ x) q) = q :=
      (chartAt ℂ x).left_inv hq.1
    exact himg ⟨(chartAt ℂ x) q, hq.2, hq_inv⟩
  · -- ℂ-level conjugacy of the pullback pair at `(chartAt ℂ x) y`, then
    -- transfer back to `X` at `y`.
    have hy2 : (chartAt ℂ x) y ∈ ball z₀ r := hy.2
    have hev : F =ᶠ[nhds ((chartAt ℂ x) y)]
        (fun w : ℂ =>
          ((potential ∘ (chartAt ℂ x).symm) w : ℂ)
            + Complex.I
              * (((fun q => (F (chartAt ℂ x q)).im) ∘ (chartAt ℂ x).symm) w
                  : ℂ)) := by
      filter_upwards [isOpen_ball.mem_nhds hy2] with w hw
      have hre : (F w).re = (potential ∘ (chartAt ℂ x).symm) w := hF_eq hw
      have him : ((fun q => (F (chartAt ℂ x q)).im) ∘ (chartAt ℂ x).symm) w
          = (F w).im := by
        show (F ((chartAt ℂ x) ((chartAt ℂ x).symm w))).im = (F w).im
        rw [(chartAt ℂ x).right_inv (hball_t hw)]
      rw [← hre, him, mul_comm]
      exact (Complex.re_add_im (F w)).symm
    have hF_d :=
      ((hF_an ((chartAt ℂ x) y) hy2).differentiableAt).hasFDerivAt
    have hpair := hF_d.congr_of_eventuallyEq hev.symm
    refine IsHarmonicConjugateAtReal.of_transfer_chart (x := x) ?_ hy.1
    refine ⟨fderiv ℂ F ((chartAt ℂ x) y), ?_⟩
    have hchart_id : ∀ w : ℂ,
        (chartAt ℂ ((chartAt ℂ x) y)).symm w = w := fun _ => rfl
    have hchart_pt :
        (chartAt ℂ ((chartAt ℂ x) y)) ((chartAt ℂ x) y) = (chartAt ℂ x) y :=
      rfl
    simp only [hchart_id, hchart_pt]
    exact hpair

end JacobianChallenge.HolomorphicForms
