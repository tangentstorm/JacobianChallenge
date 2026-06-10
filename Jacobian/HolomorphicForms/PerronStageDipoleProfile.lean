import Jacobian.HolomorphicForms.PerronStageMarkedData
import Jacobian.HolomorphicForms.HarmonicConjugate

/-!
# Stage dipole local singular profiles (Perron engine B1a)

Blueprint node: `lem:stage-dipole-local-singular-profiles`
(granular sub-node of `lem:stage-dipole-boundary-control`; subtree B1 of
`docs/perron-engine-phase1.md`).

The Perron stage boundary data is built from logarithmic dipole models at
the two marked ends.  This file packages the **local singular profiles**:
over `GenusZeroStageMarkedData` (engine A1), two functions `u0 uinf : X → ℝ`
with logarithmic singularities of sign `+1` at `P0` and `-1` at `Pinf`,
each continuous on its punctured chart source.  The marked neighborhoods
`d.U0`/`d.Uinf` lie inside the chart sources, so the profiles are honest
boundary-data germs on the separated neighborhoods of the marked points.

The bordered-stage boundary problem (normalization and compact-subdomain
bounds on the exhaustion domains, `lem:stage-dipole-boundary-control`)
remains open engine work gated on the A2 exhaustion; the off-point
harmonic-conjugate control for these single-log profiles is the B1b
follow-up.
-/

namespace JacobianChallenge.HolomorphicForms

/--
The chart-pulled-back log distance `x ↦ log ‖chartAt ℂ P x - chartAt ℂ P P‖`
is continuous on the punctured chart source `(chartAt ℂ P).source \ {P}`:
the chart is continuous on its source and injective there, so the norm is
nonvanishing away from `P` and `Real.log` composes continuously.
-/
theorem continuousOn_log_norm_chart_sub
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] (P : X) :
    ContinuousOn (fun x : X => Real.log ‖chartAt ℂ P x - (chartAt ℂ P) P‖)
      ((chartAt ℂ P).source \ {P}) := by
  have hchart : ContinuousOn (fun x : X => chartAt ℂ P x)
      ((chartAt ℂ P).source \ {P}) :=
    (chartAt ℂ P).continuousOn.mono Set.diff_subset
  have hsub : ContinuousOn
      (fun x : X => chartAt ℂ P x - (chartAt ℂ P) P)
      ((chartAt ℂ P).source \ {P}) :=
    hchart.sub continuousOn_const
  refine ContinuousOn.log hsub.norm ?_
  intro x hx
  have hx_src : x ∈ (chartAt ℂ P).source := hx.1
  have hx_ne : x ≠ P := hx.2
  have hne : chartAt ℂ P x ≠ (chartAt ℂ P) P := fun h =>
    hx_ne ((chartAt ℂ P).injOn hx_src (mem_chart_source ℂ P) h)
  simpa [norm_ne_zero_iff, sub_ne_zero] using hne

/--
Local logarithmic singular profiles at the two marked ends of the Perron
stage construction: a `+1` profile at `P0` and a `-1` profile at `Pinf`,
each continuous away from its singular point on the ambient chart source.
Only the singularity and continuity predicates are recorded — downstream
Perron/Dirichlet boundary data consumes nothing else, and the marked
neighborhoods `d.U0 ⊆ (chartAt ℂ d.P0).source`,
`d.Uinf ⊆ (chartAt ℂ d.Pinf).source` are covered by the punctured chart
sources.
-/
structure GenusZeroStageDipoleProfiles
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : X ≃ₜ OnePoint ℂ) (d : GenusZeroStageMarkedData X e) where
  /-- The local profile at the zero-marked end. -/
  u0 : X → ℝ
  /-- The local profile at the infinity-marked end. -/
  uinf : X → ℝ
  /-- `u0` has a logarithmic singularity of sign `+1` at `P0`. -/
  sing_u0 : HasLogarithmicSingularityAtReal X d.P0 u0 1
  /-- `uinf` has a logarithmic singularity of sign `-1` at `Pinf`. -/
  sing_uinf : HasLogarithmicSingularityAtReal X d.Pinf uinf (-1)
  /-- `u0` is continuous on the punctured chart source at `P0`. -/
  contOn_u0 : ContinuousOn u0 ((chartAt ℂ d.P0).source \ {d.P0})
  /-- `uinf` is continuous on the punctured chart source at `Pinf`. -/
  contOn_uinf : ContinuousOn uinf ((chartAt ℂ d.Pinf).source \ {d.Pinf})

/--
**Provider (blueprint node `lem:stage-dipole-local-singular-profiles`).**
Every marked-data package carries local singular profiles: the
chart-pulled-back log distance at `P0` (singularity by
`HasLogarithmicSingularityAtReal.log_pullback_at_pos`) and its negation at
`Pinf` (`log_pullback_at_neg`), continuous off the singular points by
`continuousOn_log_norm_chart_sub`.
-/
theorem genusZeroStageDipoleProfiles_nonempty
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : X ≃ₜ OnePoint ℂ) (d : GenusZeroStageMarkedData X e) :
    Nonempty (GenusZeroStageDipoleProfiles X e d) :=
  ⟨{ u0 := fun x : X => Real.log ‖chartAt ℂ d.P0 x - (chartAt ℂ d.P0) d.P0‖
     uinf := fun x : X =>
       -Real.log ‖chartAt ℂ d.Pinf x - (chartAt ℂ d.Pinf) d.Pinf‖
     sing_u0 := HasLogarithmicSingularityAtReal.log_pullback_at_pos d.P0
     sing_uinf := HasLogarithmicSingularityAtReal.log_pullback_at_neg d.Pinf
     contOn_u0 := continuousOn_log_norm_chart_sub d.P0
     contOn_uinf := (continuousOn_log_norm_chart_sub d.Pinf).neg }⟩

namespace GenusZeroStageDipoleProfiles

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
variable {e : X ≃ₜ OnePoint ℂ} {d : GenusZeroStageMarkedData X e}

/-- The `+1` profile is continuous on the punctured marked neighborhood. -/
theorem contOn_u0_marked (p : GenusZeroStageDipoleProfiles X e d) :
    ContinuousOn p.u0 (d.U0 \ {d.P0}) :=
  p.contOn_u0.mono (Set.diff_subset_diff_left d.U0_subset_chart)

/-- The `-1` profile is continuous on the punctured marked neighborhood. -/
theorem contOn_uinf_marked (p : GenusZeroStageDipoleProfiles X e d) :
    ContinuousOn p.uinf (d.Uinf \ {d.Pinf}) :=
  p.contOn_uinf.mono (Set.diff_subset_diff_left d.Uinf_subset_chart)

end GenusZeroStageDipoleProfiles

end JacobianChallenge.HolomorphicForms
