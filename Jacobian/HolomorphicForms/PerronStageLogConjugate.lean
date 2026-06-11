import Jacobian.HolomorphicForms.PerronStageDipolePotential

/-!
# Off-point conjugate control for single-log stage profiles (Perron engine B1b)

Blueprint node: `lem:stage-log-profile-off-point-conjugates`.

The canonical B1a/B1c stage profiles are chart-pullback single logs
`y ↦ ± log ‖chart_P y - chart_P P‖`.  jc1's B2 interface
(`StageDirichlet.lean`) consumes local harmonic conjugates at stage points
away from the marked ends (`StageHarmonicOn`).  This file supplies the
single-log mirror of the existing dipole conjugate path
(`dipole_compose_chart_has_conjugate` →
`chart_pullback_dipole_has_conjugate_at_off_PQ`): one pole, one chart
transition, a single-point slit rotation.

Outputs:

* `log_pullback_eq_compose_chart` — germ re-expression through `chart_x`;
* `log_compose_chart_has_conjugate` — the ℂ-side core (analytic transition,
  slit rotation, `Complex.log` split, normalize away `log ‖c‖`);
* `chart_pullback_log_has_conjugate_at_off_P` (+ `neg` variant) — the
  X-side off-point conjugates for the `±1` pullback logs;
* `canonicalGenusZeroStageDipoleProfiles` and conjugate corollaries: the
  canonical profiles, and the glued potential of B1c, admit local
  harmonic conjugates at every point of the punctured marked
  neighborhoods — the `StageHarmonicOn`-shaped facts on `U0 \ {P0}` and
  `Uinf \ {Pinf}`.
-/

namespace JacobianChallenge.HolomorphicForms

open Filter Set

/-- Single-log mirror of `dipole_pullback_eq_compose_chart`: near any
`x`, the chart-pullback log agrees with its re-expression through the
chart at `x`. -/
lemma log_pullback_eq_compose_chart
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (P x : X) :
    (fun y : X => Real.log ‖chartAt ℂ P y - (chartAt ℂ P) P‖)
    =ᶠ[nhds x]
    (fun y : X =>
        Real.log ‖chartAt ℂ P ((chartAt ℂ x).symm (chartAt ℂ x y))
                   - (chartAt ℂ P) P‖) := by
  have hsrc_nhds : (chartAt ℂ x).source ∈ nhds x :=
    (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)
  filter_upwards [hsrc_nhds] with y hy
  rw [(chartAt ℂ x).left_inv hy]

/-- ℂ-side core, single-log mirror of `dipole_compose_chart_has_conjugate`:
the re-expressed log `z ↦ log ‖chart_P (chart_x.symm z) - chart_P P‖`
admits a local harmonic conjugate at `chart_x x`.  The conjugate is
`arg (c * h_P ·)` for a slit rotation `c`; the analytic witness is
`Complex.log (c * h_P ·) - log ‖c‖`. -/
theorem log_compose_chart_has_conjugate
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    {P x : X} (hxP : x ≠ P)
    (hxP_src : x ∈ (chartAt ℂ P).source) :
    ∃ v_ℂ : ℂ → ℝ,
      IsHarmonicConjugateAtReal ℂ
        (fun z : ℂ =>
          Real.log ‖chartAt ℂ P ((chartAt ℂ x).symm z) - (chartAt ℂ P) P‖)
        v_ℂ ((chartAt ℂ x) x) := by
  have hxinv : (chartAt ℂ x).symm ((chartAt ℂ x) x) = x :=
    (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
  have hxt : (chartAt ℂ x) x ∈ (chartAt ℂ x).target :=
    (chartAt ℂ x).map_source (mem_chart_source ℂ x)
  have hxP_pre : (chartAt ℂ x) x ∈ (chartAt ℂ x).symm ⁻¹' (chartAt ℂ P).source := by
    rw [Set.mem_preimage, hxinv]; exact hxP_src
  have hP_open : IsOpen ((chartAt ℂ x).target ∩
      (chartAt ℂ x).symm ⁻¹' (chartAt ℂ P).source) :=
    (chartAt ℂ x).continuousOn_symm.isOpen_inter_preimage
      (chartAt ℂ x).open_target (chartAt ℂ P).open_source
  have hxP_in : (chartAt ℂ x) x ∈
      (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (chartAt ℂ P).source :=
    Set.mem_inter hxt hxP_pre
  have hP_an : AnalyticAt ℂ (chartAt ℂ P ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) :=
    AnalyticOn.analyticAt (hP_open.mem_nhds hxP_in)
      (chart_transition_contDiffOn x P).analyticOn
  have hP_h : AnalyticAt ℂ
      (fun z => chartAt ℂ P ((chartAt ℂ x).symm z) - (chartAt ℂ P) P)
      ((chartAt ℂ x) x) := hP_an.sub analyticAt_const
  have hP_ne : chartAt ℂ P x - (chartAt ℂ P) P ≠ 0 := fun h =>
    hxP ((chartAt ℂ P).injOn hxP_src (mem_chart_source ℂ P) (sub_eq_zero.mp h))
  obtain ⟨c, hcP_slit, -⟩ := slit_rotation_for_two_nonzero hP_ne hP_ne
  have hc_ne : c ≠ 0 := fun hc0 => by
    rw [hc0, zero_mul] at hcP_slit; exact Complex.zero_notMem_slitPlane hcP_slit
  have hcP_val : c * (chartAt ℂ P ((chartAt ℂ x).symm ((chartAt ℂ x) x))
                      - (chartAt ℂ P) P) ∈ Complex.slitPlane := by
    rw [hxinv]; exact hcP_slit
  have hPmul_an : AnalyticAt ℂ
      (fun z => c * (chartAt ℂ P ((chartAt ℂ x).symm z) - (chartAt ℂ P) P))
      ((chartAt ℂ x) x) := analyticAt_const.mul hP_h
  have hPlog_an : AnalyticAt ℂ
      (fun z => Complex.log (c * (chartAt ℂ P ((chartAt ℂ x).symm z)
                                   - (chartAt ℂ P) P)))
      ((chartAt ℂ x) x) := AnalyticAt.clog hPmul_an hcP_val
  have hftotal_an : AnalyticAt ℂ
      (fun z =>
        Complex.log (c * (chartAt ℂ P ((chartAt ℂ x).symm z) - (chartAt ℂ P) P))
        - (Real.log ‖c‖ : ℂ))
      ((chartAt ℂ x) x) := hPlog_an.sub analyticAt_const
  have hftotal_fderiv := hftotal_an.differentiableAt.hasFDerivAt
  set v_ℂ : ℂ → ℝ := fun z =>
    Complex.arg (c * (chartAt ℂ P ((chartAt ℂ x).symm z) - (chartAt ℂ P) P))
    with hv_def
  have hcontP : ContinuousAt
      (fun z => c * (chartAt ℂ P ((chartAt ℂ x).symm z) - (chartAt ℂ P) P))
      ((chartAt ℂ x) x) :=
    (continuous_const.continuousAt).mul hP_h.continuousAt
  have hPnbhd : (fun z => c * (chartAt ℂ P ((chartAt ℂ x).symm z)
                                  - (chartAt ℂ P) P)) ⁻¹' Complex.slitPlane
                ∈ nhds ((chartAt ℂ x) x) :=
    hcontP.preimage_mem_nhds (Complex.isOpen_slitPlane.mem_nhds hcP_val)
  have hfeq : (fun z =>
        Complex.log (c * (chartAt ℂ P ((chartAt ℂ x).symm z) - (chartAt ℂ P) P))
        - (Real.log ‖c‖ : ℂ))
      =ᶠ[nhds ((chartAt ℂ x) x)]
      (fun z =>
        ((Real.log ‖chartAt ℂ P ((chartAt ℂ x).symm z) - (chartAt ℂ P) P‖ : ℝ) : ℂ)
        + Complex.I * (v_ℂ z : ℂ)) := by
    filter_upwards [hPnbhd] with z hzP
    have hzP_ne : c * (chartAt ℂ P ((chartAt ℂ x).symm z) - (chartAt ℂ P) P) ≠ 0 :=
      fun h => Complex.zero_notMem_slitPlane (h ▸ hzP)
    have hhP_ne : chartAt ℂ P ((chartAt ℂ x).symm z) - (chartAt ℂ P) P ≠ 0 :=
      fun h => hzP_ne (by rw [h, mul_zero])
    show Complex.log (c * (chartAt ℂ P ((chartAt ℂ x).symm z) - (chartAt ℂ P) P))
          - (Real.log ‖c‖ : ℂ)
        = ((Real.log ‖chartAt ℂ P ((chartAt ℂ x).symm z) - (chartAt ℂ P) P‖ : ℝ) : ℂ)
          + Complex.I * (v_ℂ z : ℂ)
    simp only [Complex.log, norm_mul, hv_def,
               Real.log_mul (norm_ne_zero_iff.mpr hc_ne)
                            (norm_ne_zero_iff.mpr hhP_ne)]
    push_cast
    ring
  refine ⟨v_ℂ, fderiv ℂ
      (fun z =>
        Complex.log (c * (chartAt ℂ P ((chartAt ℂ x).symm z) - (chartAt ℂ P) P))
        - (Real.log ‖c‖ : ℂ))
      ((chartAt ℂ x) x), ?_⟩
  have hchart_ℂ_id : ∀ z : ℂ, (chartAt ℂ ((chartAt ℂ x) x)).symm z = z := fun _ => rfl
  have hchart_ℂ_pt :
      (chartAt ℂ ((chartAt ℂ x) x)) ((chartAt ℂ x) x) = (chartAt ℂ x) x := rfl
  simp only [hchart_ℂ_id, hchart_ℂ_pt]
  exact hftotal_fderiv.congr_of_eventuallyEq hfeq.symm

/-- X-side off-point conjugate for the `+1` chart-pullback log, single-log
mirror of `chart_pullback_dipole_has_conjugate_at_off_PQ`. -/
theorem chart_pullback_log_has_conjugate_at_off_P
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    {P x : X} (hxP : x ≠ P)
    (hxP_src : x ∈ (chartAt ℂ P).source) :
    ∃ v : X → ℝ,
      IsHarmonicConjugateAtReal X
        (fun y : X => Real.log ‖chartAt ℂ P y - (chartAt ℂ P) P‖) v x := by
  obtain ⟨v_ℂ, h_conj⟩ := log_compose_chart_has_conjugate hxP hxP_src
  have h_X : IsHarmonicConjugateAtReal X
      ((fun z : ℂ =>
          Real.log ‖chartAt ℂ P ((chartAt ℂ x).symm z) - (chartAt ℂ P) P‖)
        ∘ chartAt ℂ x)
      (v_ℂ ∘ chartAt ℂ x) x :=
    IsHarmonicConjugateAtReal.chart_pullback_lift_at_basepoint
      (P := x) h_conj
  refine ⟨v_ℂ ∘ chartAt ℂ x, ?_⟩
  exact h_X.congr_of_eventuallyEq
    (log_pullback_eq_compose_chart P x).symm
    (Filter.EventuallyEq.refl _ _)

/-- X-side off-point conjugate for the `-1` chart-pullback log: negate. -/
theorem chart_pullback_neg_log_has_conjugate_at_off_P
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    {P x : X} (hxP : x ≠ P)
    (hxP_src : x ∈ (chartAt ℂ P).source) :
    ∃ v : X → ℝ,
      IsHarmonicConjugateAtReal X
        (fun y : X => -Real.log ‖chartAt ℂ P y - (chartAt ℂ P) P‖) v x := by
  obtain ⟨v, hv⟩ := chart_pullback_log_has_conjugate_at_off_P hxP hxP_src
  refine ⟨fun y => -(v y), ?_⟩
  have h := hv.neg
  exact h.congr_of_eventuallyEq
    (Filter.EventuallyEq.refl _ _) (Filter.EventuallyEq.refl _ _)

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
variable {e : X ≃ₜ OnePoint ℂ}

/-- The canonical B1a profiles as a definition (the provider
`genusZeroStageDipoleProfiles_nonempty` exports only `Nonempty`; downstream
conjugate corollaries need the concrete chart-pullback-log witnesses). -/
noncomputable def canonicalGenusZeroStageDipoleProfiles
    (d : GenusZeroStageMarkedData X e) :
    GenusZeroStageDipoleProfiles X e d where
  u0 := fun x : X => Real.log ‖chartAt ℂ d.P0 x - (chartAt ℂ d.P0) d.P0‖
  uinf := fun x : X =>
    -Real.log ‖chartAt ℂ d.Pinf x - (chartAt ℂ d.Pinf) d.Pinf‖
  sing_u0 := HasLogarithmicSingularityAtReal.log_pullback_at_pos d.P0
  sing_uinf := HasLogarithmicSingularityAtReal.log_pullback_at_neg d.Pinf
  contOn_u0 := continuousOn_log_norm_chart_sub d.P0
  contOn_uinf := (continuousOn_log_norm_chart_sub d.Pinf).neg

section Canonical

variable [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
variable (d : GenusZeroStageMarkedData X e)

/-- The canonical `+1` profile admits a local harmonic conjugate at every
point of its punctured chart source. -/
theorem canonical_u0_has_conjugate_at
    {x : X} (hx : x ∈ (chartAt ℂ d.P0).source \ {d.P0}) :
    ∃ v : X → ℝ,
      IsHarmonicConjugateAtReal X
        (canonicalGenusZeroStageDipoleProfiles d).u0 v x :=
  chart_pullback_log_has_conjugate_at_off_P hx.2 hx.1

/-- The canonical `-1` profile admits a local harmonic conjugate at every
point of its punctured chart source. -/
theorem canonical_uinf_has_conjugate_at
    {x : X} (hx : x ∈ (chartAt ℂ d.Pinf).source \ {d.Pinf}) :
    ∃ v : X → ℝ,
      IsHarmonicConjugateAtReal X
        (canonicalGenusZeroStageDipoleProfiles d).uinf v x :=
  chart_pullback_neg_log_has_conjugate_at_off_P hx.2 hx.1

/-- The glued stage dipole potential over the canonical profiles admits a
local harmonic conjugate at every point of the punctured `U0`: the
`StageHarmonicOn`-shaped fact on the zero-marked neighborhood. -/
theorem stageDipoleGluedPotential_canonical_has_conjugate_on_U0
    {x : X} (hxU : x ∈ d.U0) (hxP : x ≠ d.P0) :
    ∃ v : X → ℝ,
      IsHarmonicConjugateAtReal X
        (stageDipoleGluedPotential d (canonicalGenusZeroStageDipoleProfiles d))
        v x := by
  have hx_src : x ∈ (chartAt ℂ d.P0).source := d.U0_subset_chart hxU
  obtain ⟨v, hv⟩ := canonical_u0_has_conjugate_at d ⟨hx_src, hxP⟩
  refine ⟨v, ?_⟩
  have hglue_eq :
      (canonicalGenusZeroStageDipoleProfiles d).u0
      =ᶠ[nhds x]
      stageDipoleGluedPotential d (canonicalGenusZeroStageDipoleProfiles d) := by
    filter_upwards [d.isOpen_U0.mem_nhds hxU] with y hy
    exact (stageDipoleGluedPotential.eqOn_u0 d
      (canonicalGenusZeroStageDipoleProfiles d) hy).symm
  exact hv.congr_of_eventuallyEq hglue_eq (Filter.EventuallyEq.refl _ _)

/-- The glued stage dipole potential over the canonical profiles admits a
local harmonic conjugate at every point of the punctured `Uinf`: the
`StageHarmonicOn`-shaped fact on the infinity-marked neighborhood. -/
theorem stageDipoleGluedPotential_canonical_has_conjugate_on_Uinf
    {x : X} (hxU : x ∈ d.Uinf) (hxP : x ≠ d.Pinf) :
    ∃ v : X → ℝ,
      IsHarmonicConjugateAtReal X
        (stageDipoleGluedPotential d (canonicalGenusZeroStageDipoleProfiles d))
        v x := by
  have hx_src : x ∈ (chartAt ℂ d.Pinf).source := d.Uinf_subset_chart hxU
  obtain ⟨v, hv⟩ := canonical_uinf_has_conjugate_at d ⟨hx_src, hxP⟩
  refine ⟨v, ?_⟩
  have hglue_eq :
      (canonicalGenusZeroStageDipoleProfiles d).uinf
      =ᶠ[nhds x]
      stageDipoleGluedPotential d (canonicalGenusZeroStageDipoleProfiles d) := by
    filter_upwards [d.isOpen_Uinf.mem_nhds hxU] with y hy
    exact (stageDipoleGluedPotential.eqOn_uinf d
      (canonicalGenusZeroStageDipoleProfiles d) hy).symm
  exact hv.congr_of_eventuallyEq hglue_eq (Filter.EventuallyEq.refl _ _)

end Canonical

end JacobianChallenge.HolomorphicForms
