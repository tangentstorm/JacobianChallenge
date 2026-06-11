import Jacobian.HolomorphicForms.PerronStageDipoleProfile

/-!
# Glued stage dipole potential (Perron engine B1c)

Blueprint node: `lem:stage-dipole-glued-potential`.

jc1's boundary-control interface (`StageDipoleBoundary.lean`) needs, at its
core, one real potential carrying simultaneously: base normalization, the
`+1` logarithmic singularity at `P0`, the `-1` singularity at `Pinf`, and
exact agreement with the B1a local profiles near the marked points.  This
file provides that core, stage-independently.

The construction exploits that the A1 marked neighborhoods `U0`, `Uinf`,
`Ubase` are **pairwise disjoint**: the case-glue

`x ↦ if x ∈ U0 then u0 x else if x ∈ Uinf then uinf x else 0`

is well-defined, vanishes at `base` (disjointness with `Ubase`), agrees
with each profile on its full neighborhood, and inherits each profile's
singularity because `HasLogarithmicSingularityAtReal` is a germ predicate
at the marked point — made precise by the new congruence helper
`HasLogarithmicSingularityAtReal.congr_on_nhds`.

The genuinely A2-gated remainder of the boundary-control obligation
(per-stage finite boundary-chart bounds and compact-subdomain bounds)
is NOT addressed here.
-/

namespace JacobianChallenge.HolomorphicForms

open Filter Set

/--
`HasLogarithmicSingularityAtReal` is a germ predicate: it transfers along
agreement on any neighborhood of the singular point.
-/
theorem HasLogarithmicSingularityAtReal.congr_on_nhds
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {P : X} {u v : X → ℝ} {sign : ℝ} {U : Set X}
    (h : HasLogarithmicSingularityAtReal X P u sign)
    (hU : U ∈ nhds P) (huv : Set.EqOn u v U) :
    HasLogarithmicSingularityAtReal X P v sign := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  have hP_eq : (chartAt ℂ P).symm ((chartAt ℂ P) P) = P :=
    (chartAt ℂ P).left_inv (mem_chart_source ℂ P)
  have hsymm_cont : ContinuousAt (chartAt ℂ P).symm ((chartAt ℂ P) P) :=
    (chartAt ℂ P).continuousAt_symm
      ((chartAt ℂ P).map_source (mem_chart_source ℂ P))
  have hmem : (chartAt ℂ P).symm ⁻¹' U ∈ nhds ((chartAt ℂ P) P) := by
    apply hsymm_cont.preimage_mem_nhds
    rw [hP_eq]
    exact hU
  have heq :
      (fun z : ℂ =>
        u ((chartAt ℂ P).symm z) - sign * Real.log ‖z - (chartAt ℂ P) P‖)
      =ᶠ[nhds ((chartAt ℂ P) P)]
      (fun z : ℂ =>
        v ((chartAt ℂ P).symm z) - sign * Real.log ‖z - (chartAt ℂ P) P‖) := by
    filter_upwards [hmem] with z hz
    rw [huv hz]
  exact hc.congr' heq

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
variable {e : X ≃ₜ OnePoint ℂ}

open Classical in
/--
The glued stage dipole potential: the `+1` profile on `U0`, the `-1`
profile on `Uinf`, and `0` elsewhere — well-defined because the marked
neighborhoods are pairwise disjoint.
-/
noncomputable def stageDipoleGluedPotential
    (d : GenusZeroStageMarkedData X e)
    (p : GenusZeroStageDipoleProfiles X e d) : X → ℝ :=
  fun x => if x ∈ d.U0 then p.u0 x else if x ∈ d.Uinf then p.uinf x else 0

namespace stageDipoleGluedPotential

variable (d : GenusZeroStageMarkedData X e)
variable (p : GenusZeroStageDipoleProfiles X e d)

/-- The glued potential agrees with the `+1` profile on all of `U0`. -/
theorem eqOn_u0 : Set.EqOn (stageDipoleGluedPotential d p) p.u0 d.U0 := by
  intro x hx
  simp only [stageDipoleGluedPotential, if_pos hx]

/-- The glued potential agrees with the `-1` profile on all of `Uinf`. -/
theorem eqOn_uinf :
    Set.EqOn (stageDipoleGluedPotential d p) p.uinf d.Uinf := by
  intro x hx
  have h0 : x ∉ d.U0 := Set.disjoint_right.mp d.disjoint_U0_Uinf hx
  simp only [stageDipoleGluedPotential, if_neg h0, if_pos hx]

/-- The glued potential vanishes at the base normalization point. -/
theorem base_eq_zero : stageDipoleGluedPotential d p d.base = 0 := by
  have h0 : d.base ∉ d.U0 :=
    Set.disjoint_right.mp d.disjoint_U0_Ubase d.mem_Ubase
  have hinf : d.base ∉ d.Uinf :=
    Set.disjoint_right.mp d.disjoint_Uinf_Ubase d.mem_Ubase
  simp only [stageDipoleGluedPotential, if_neg h0, if_neg hinf]

/-- The glued potential keeps the `+1` logarithmic singularity at `P0`. -/
theorem sing_P0 :
    HasLogarithmicSingularityAtReal X d.P0
      (stageDipoleGluedPotential d p) 1 :=
  p.sing_u0.congr_on_nhds (d.isOpen_U0.mem_nhds d.mem_U0)
    (eqOn_u0 d p).symm

/-- The glued potential keeps the `-1` logarithmic singularity at `Pinf`. -/
theorem sing_Pinf :
    HasLogarithmicSingularityAtReal X d.Pinf
      (stageDipoleGluedPotential d p) (-1) :=
  p.sing_uinf.congr_on_nhds (d.isOpen_Uinf.mem_nhds d.mem_Uinf)
    (eqOn_uinf d p).symm

end stageDipoleGluedPotential

/--
Stage-independent core payload of the dipole boundary-control interface:
one potential carrying base normalization, both marked-end logarithmic
singularities, and agreement with the B1a local profiles near the marked
points.  Field names mirror `StageDipoleBoundaryControl`; the per-stage
finite boundary-chart and compact-subdomain bounds are the remaining
(A2-gated) frontier content.
-/
structure StageDipolePotentialData
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : X ≃ₜ OnePoint ℂ)
    (marked : GenusZeroStageMarkedData X e)
    (profiles : GenusZeroStageDipoleProfiles X e marked) where
  /-- The boundary potential core. -/
  potential : X → ℝ
  /-- Normalization at the marked base point. -/
  base_normalized : potential marked.base = 0
  /-- The `+1` logarithmic singularity at the zero-marked end. -/
  has_pos_log_profile :
    HasLogarithmicSingularityAtReal X marked.P0 potential 1
  /-- The `-1` logarithmic singularity at the infinity-marked end. -/
  has_neg_log_profile :
    HasLogarithmicSingularityAtReal X marked.Pinf potential (-1)
  /-- Agreement with the `+1` local profile near `P0`. -/
  agrees_with_u0_near_P0 :
    Set.EqOn potential profiles.u0 (marked.U0 \ {marked.P0})
  /-- Agreement with the `-1` local profile near `Pinf`. -/
  agrees_with_uinf_near_Pinf :
    Set.EqOn potential profiles.uinf (marked.Uinf \ {marked.Pinf})

/--
**Provider (blueprint node `lem:stage-dipole-glued-potential`).**
Every marked-data package with local profiles carries the boundary-control
core payload, witnessed by the glued potential.
-/
theorem stageDipolePotentialData_nonempty
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : X ≃ₜ OnePoint ℂ)
    (marked : GenusZeroStageMarkedData X e)
    (profiles : GenusZeroStageDipoleProfiles X e marked) :
    Nonempty (StageDipolePotentialData X e marked profiles) :=
  ⟨{ potential := stageDipoleGluedPotential marked profiles
     base_normalized := stageDipoleGluedPotential.base_eq_zero marked profiles
     has_pos_log_profile := stageDipoleGluedPotential.sing_P0 marked profiles
     has_neg_log_profile := stageDipoleGluedPotential.sing_Pinf marked profiles
     agrees_with_u0_near_P0 :=
       (stageDipoleGluedPotential.eqOn_u0 marked profiles).mono
         Set.diff_subset
     agrees_with_uinf_near_Pinf :=
       (stageDipoleGluedPotential.eqOn_uinf marked profiles).mono
         Set.diff_subset }⟩

end JacobianChallenge.HolomorphicForms
