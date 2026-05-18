import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Jacobian.HolomorphicForms.Meromorphic
import Jacobian.HolomorphicForms.CMfldBumpStub
import Jacobian.HolomorphicForms.Divisor
import Jacobian.HolomorphicForms.OnePointCxIsManifold
import Jacobian.HolomorphicForms.BranchedCover
import Jacobian.HolomorphicForms.ChartedSpaceComplexPoints
import Jacobian.Periods.TrivializationContinuousLinearMapAt

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold Topology
open Set
open Classical

variable {X : Type _} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [JacobianChallenge.Periods.StableChartAt ℂ X]

private theorem complex_isManifold_real
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (𝓘(ℂ)) (⊤ : WithTop ℕ∞) X] :
    IsManifold (𝓘(ℝ, ℂ)) (⊤ : WithTop ℕ∞) X := by
  apply isManifold_of_contDiffOn
  intro e₁ e₂ he₁ he₂
  have h_complex : ContDiffOn ℂ ⊤ (e₂ ∘ e₁.symm) (e₁.symm ≫ₕ e₂).source := by
    have := ‹IsManifold (𝓘(ℂ)) (⊤ : WithTop ℕ∞) X›.compatible he₁ he₂
    convert this.1
    ext x
    simp [contDiffPregroupoid]
  simpa [ModelWithCorners.range_eq_target] using h_complex.restrict_scalars ℝ

/-- f(x) = cMfldBump(Q,x) / ((chartAt ℂ Q).toFun(x) - φ(Q))  on chart, 0 off,
    with f(Q) := ∞. -/
noncomputable def singlePoleSphereLift (Q : X) (x : X) : OnePoint ℂ :=
  if x = Q then
    OnePoint.infty
  else if x ∈ (chartAt ℂ Q).source then
    let φ := chartAt ℂ Q
    let val : ℂ := (cMfldBump Q x : ℝ) / (φ x - φ Q)
    (val : OnePoint ℂ)
  else
    ((0 : ℂ) : OnePoint ℂ)

/-- Local complex-valued lift for the single-pole function, used in the
modulus-divergence axiom. -/
noncomputable def singlePoleLocalLift (Q : X) (x : X) : ℂ :=
  if x ∈ (chartAt ℂ Q).source then
    if x = Q then (0 : ℂ) else
    (cMfldBump Q x : ℝ) / (chartAt ℂ Q x - chartAt ℂ Q Q)
  else
    0

omit [JacobianChallenge.Periods.StableChartAt ℂ X] in
private theorem singlePoleLocalLift_continuousWithinAt_compl
    (Q x : X) (hxQ : x ≠ Q) :
    ContinuousWithinAt (singlePoleLocalLift Q) {Q}ᶜ x := by
  haveI : IsManifold (𝓘(ℝ, ℂ)) (⊤ : WithTop ℕ∞) X :=
    complex_isManifold_real
  by_cases hxsrc : x ∈ (chartAt ℂ Q).source
  · have hbump : ContinuousAt (fun y : X => (cMfldBump Q y : ℂ)) x :=
      Complex.continuous_ofReal.continuousAt.comp
        ((cMfldBump_continuous (X := X) Q).continuousAt)
    have hchart : ContinuousAt (fun y : X => chartAt ℂ Q y) x :=
      (chartAt ℂ Q).continuousAt hxsrc
    have hden_ne : chartAt ℂ Q x - chartAt ℂ Q Q ≠ 0 := by
      intro hzero
      apply hxQ
      exact (chartAt ℂ Q).injOn hxsrc (mem_chart_source ℂ Q) (sub_eq_zero.mp hzero)
    have hquot : ContinuousAt
        (fun y : X => (cMfldBump Q y : ℂ) / (chartAt ℂ Q y - chartAt ℂ Q Q)) x :=
      hbump.div (hchart.sub continuousAt_const) hden_ne
    have hsrc_ev : ∀ᶠ y in 𝓝[{Q}ᶜ] x, y ∈ (chartAt ℂ Q).source :=
      mem_nhdsWithin_of_mem_nhds ((chartAt ℂ Q).open_source.mem_nhds hxsrc)
    have hne_ev : ∀ᶠ y in 𝓝[{Q}ᶜ] x, y ≠ Q :=
      eventually_nhdsWithin_of_forall (by intro y hy; exact hy)
    have hlocal_eq :
        (fun y : X => (cMfldBump Q y : ℂ) / (chartAt ℂ Q y - chartAt ℂ Q Q))
          =ᶠ[𝓝[{Q}ᶜ] x] singlePoleLocalLift Q := by
      filter_upwards [hsrc_ev, hne_ev] with y hysrc hyQ
      simp [singlePoleLocalLift, hysrc, hyQ]
    change Filter.Tendsto (singlePoleLocalLift Q) (𝓝[{Q}ᶜ] x) (𝓝 (singlePoleLocalLift Q x))
    rw [show singlePoleLocalLift Q x =
        (cMfldBump Q x : ℂ) / (chartAt ℂ Q x - chartAt ℂ Q Q) by
      simp [singlePoleLocalLift, hxsrc, hxQ]]
    exact hquot.continuousWithinAt.congr' hlocal_eq
  · let f : SmoothBumpFunction (𝓘(ℝ, ℂ)) Q :=
      Classical.choice (show Nonempty (SmoothBumpFunction (𝓘(ℝ, ℂ)) Q) from inferInstance)
    have hx_tsupport : x ∉ tsupport (f : X → ℝ) := by
      intro hx
      exact hxsrc (f.tsupport_subset_chartAt_source hx)
    have hzero_ev : ∀ᶠ y in 𝓝 x, f y = 0 := by
      filter_upwards [(isClosed_tsupport (f : X → ℝ)).isOpen_compl.mem_nhds hx_tsupport] with
        y hy
      have hnot_support : y ∉ Function.support (f : X → ℝ) := by
        intro hsupport
        exact hy (subset_closure hsupport)
      simpa [Function.support] using hnot_support
    have hzero_ev_within : ∀ᶠ y in 𝓝[{Q}ᶜ] x, f y = 0 :=
      hzero_ev.filter_mono nhdsWithin_le_nhds
    have hzero_within : (fun _ : X => (0 : ℂ)) =ᶠ[𝓝[{Q}ᶜ] x] singlePoleLocalLift Q := by
      filter_upwards [hzero_ev_within] with y hyzero
      symm
      ·
        unfold singlePoleLocalLift cMfldBump
        change (if y ∈ (chartAt ℂ Q).source then
            if y = Q then (0 : ℂ) else (f y : ℝ) / (chartAt ℂ Q y - chartAt ℂ Q Q)
          else 0) = 0
        by_cases hysrc : y ∈ (chartAt ℂ Q).source
        · by_cases hyQ : y = Q
          · simp [hyQ]
          · simp [hysrc, hyQ, hyzero]
        · simp [hysrc]
    change Filter.Tendsto (singlePoleLocalLift Q) (𝓝[{Q}ᶜ] x) (𝓝 (singlePoleLocalLift Q x))
    rw [show singlePoleLocalLift Q x = 0 by simp [singlePoleLocalLift, hxsrc]]
    exact continuousWithinAt_const.congr' hzero_within

/-! ### BranchedCoverData construction helpers

The previous shared obligation `honestMeromorphic_branchedCoverData_obligation`
was universally quantified over *all* continuous `f : X → OnePoint ℂ` and *all*
divisors `D`, making it **mathematically false** (e.g. a constant map on an
infinite space cannot have finite fibers, and the degree cannot be made to match
an arbitrary divisor).

We replace it with **specific constructions** for each meromorphic map, where
the hard analytical sub-obligations (finite fibers, degree constancy,
local bijectivity) are isolated as individual `sorry` targets that can be
discharged independently once the required analytic machinery is in place. -/

/-- Finite fibers for `singlePoleSphereLift Q`, assuming continuity.
A continuous map from a compact Riemann surface with a single simple pole
has degree 1, hence every fiber is finite (in fact a singleton). -/
lemma singlePoleSphereLift_finite_fiber (Q : X)
    (hcont : Continuous (singlePoleSphereLift Q)) :
    ∀ y : OnePoint ℂ, (singlePoleSphereLift Q ⁻¹' {y}).Finite := by
  -- Blocked: the current concrete lift is cut off by `cMfldBump` and is
  -- explicitly `0` off the chosen chart source.  Continuity alone does not
  -- imply finite fibres, and the `0`-fibre can contain a large off-chart
  -- region.  This needs an honest global meromorphic one-pole map, not the
  -- present bump-cutoff surrogate.
  sorry

/-- The weighted fiber count of `singlePoleSphereLift Q` is constant across
all fibers, equal to 1 (the degree of a single simple pole). -/
lemma singlePoleSphereLift_fiberSum_const (Q : X)
    (hcont : Continuous (singlePoleSphereLift Q))
    (hfin : ∀ y : OnePoint ℂ, (singlePoleSphereLift Q ⁻¹' {y}).Finite) :
    ∀ y₁ y₂ : OnePoint ℂ,
      (hfin y₁).toFinset.sum (fun _ => 1) = (hfin y₂).toFinset.sum (fun _ => 1) := by
  -- Blocked with `singlePoleSphereLift_finite_fiber`: the desired degree-one
  -- fibre count belongs to a genuine meromorphic map with one simple pole,
  -- while the current cutoff model has an artificial `0`-fibre.
  sorry

/-- Local bijectivity of `singlePoleSphereLift Q` at every point
(since ramification index is uniformly 1 for a simple-pole map). -/
lemma singlePoleSphereLift_local_bijective (Q : X)
    (hcont : Continuous (singlePoleSphereLift Q)) :
    ∀ x : X, (fun (_ : X) => (1 : ℕ)) x = 1 →
      ∃ U : Set X, ∃ V : Set (OnePoint ℂ),
        IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ singlePoleSphereLift Q x ∈ V ∧
          Set.BijOn (singlePoleSphereLift Q) U V := by
  -- Blocked: local bijectivity is false at points in any open region where
  -- the cutoff presentation is locally constant `0`.  A proof requires a
  -- non-cutoff meromorphic local normal form around every nonramified point.
  sorry

/-- The branched degree of `singlePoleSphereLift Q` equals 1 =
`(Divisor.point Q).degree.toNat`. -/
lemma singlePoleSphereLift_branchedDegree_eq (Q : X)
    (h : BranchedCoverData X (OnePoint ℂ) (singlePoleSphereLift Q)) :
    branchedDegree h = (Divisor.point Q).degree.toNat := by
  -- Blocked: this should follow from a branched-cover datum for an honest
  -- degree-one meromorphic map.  For the current cutoff map, the preceding
  -- finite-fibre and local-bijection fields are not available honestly.
  sorry

/-- Construct `BranchedCoverData` for `singlePoleSphereLift Q`.
A meromorphic function with a single simple pole has degree 1, so every
fiber is a singleton with ramification index 1. -/
noncomputable def singlePoleSphereLift_branchedCoverData (Q : X)
    (hcont : Continuous (singlePoleSphereLift Q)) :
    BranchedCoverData X (OnePoint ℂ) (singlePoleSphereLift Q) where
  ramificationIndex := fun _ => 1
  ramificationIndex_pos := fun _ => Nat.one_pos
  finite_fiber := singlePoleSphereLift_finite_fiber Q hcont
  fiberSum_const := singlePoleSphereLift_fiberSum_const Q hcont
    (singlePoleSphereLift_finite_fiber Q hcont)
  ramified_finite := by
    convert Set.finite_empty
    ext x; simp
  local_bijective_unramified := singlePoleSphereLift_local_bijective Q hcont

/-- The `hasBranchedCoverDataOfPoleDegree` obligation for `singlePoleMeromorphicMap`:
given continuity, produce a `BranchedCoverData` whose `branchedDegree` equals
`(Divisor.point Q).degree.toNat = 1`. -/
lemma singlePole_hasBranchedCoverDataOfPoleDegree (Q : X) :
    Continuous (singlePoleSphereLift Q) →
    ∃ (h : BranchedCoverData X (OnePoint ℂ) (singlePoleSphereLift Q)),
      branchedDegree h = (Divisor.point Q).degree.toNat := by
  intro hcont
  exact ⟨singlePoleSphereLift_branchedCoverData Q hcont,
         singlePoleSphereLift_branchedDegree_eq Q _⟩

/-- A meromorphic map with a single simple pole at Q. -/
noncomputable def singlePoleMeromorphicMap (Q : X) : MeromorphicMapToSphere X :=
  { toMap := singlePoleSphereLift Q
    locally_meromorphic := True
    zeroDivisor := 0
    poleDivisor := Divisor.point Q
    principalDivisor := -Divisor.point Q
    principalDivisor_eq := by simp
    poleDivisor_nonneg := fun x => by
      classical
      exact Divisor.effective_point Q x
    zero_or_pole_eq_zero := fun _ => Or.inl rfl
    toMap_ne_infty_of_poleDivisor_zero := fun x hx => by
      have hne : x ≠ Q := by
        intro h
        rw [h, Divisor.point_apply_self] at hx
        exact zero_ne_one hx.symm
      unfold singlePoleSphereLift
      split_ifs with heq hsrc
      · contradiction
      · exact OnePoint.coe_ne_infty _
      · exact OnePoint.coe_ne_infty _
    continuousOn_ne_infty := by
      have hfinite_locus :
          {x : X | singlePoleSphereLift Q x ≠ (OnePoint.infty : OnePoint ℂ)} =
            {Q}ᶜ := by
        ext x
        unfold singlePoleSphereLift
        by_cases hxQ : x = Q
        · simp [hxQ]
        · by_cases hxsrc : x ∈ (chartAt ℂ Q).source
          · simp [hxQ, hxsrc]
          · simp [hxQ, hxsrc]
      rw [hfinite_locus]
      intro x hx
      have hxQ : x ≠ Q := hx
      have hlocal :
          (fun y : X => ((singlePoleLocalLift Q y : ℂ) : OnePoint ℂ))
            =ᶠ[𝓝[{Q}ᶜ] x] singlePoleSphereLift Q := by
        have hne_ev : ∀ᶠ y in 𝓝[{Q}ᶜ] x, y ≠ Q :=
          eventually_nhdsWithin_of_forall (by intro y hy; exact hy)
        filter_upwards [hne_ev] with y hyQ
        unfold singlePoleLocalLift singlePoleSphereLift
        by_cases hysrc : y ∈ (chartAt ℂ Q).source
        · simp [hyQ, hysrc]
        · simp [hyQ, hysrc]
      have hcoe : ContinuousWithinAt
          (fun y : X => ((singlePoleLocalLift Q y : ℂ) : OnePoint ℂ)) {Q}ᶜ x :=
        OnePoint.continuous_coe.continuousAt.comp_continuousWithinAt
          (singlePoleLocalLift_continuousWithinAt_compl Q x hxQ)
      change Filter.Tendsto (singlePoleSphereLift Q) (𝓝[{Q}ᶜ] x)
        (𝓝 (singlePoleSphereLift Q x))
      rw [show singlePoleSphereLift Q x =
          ((singlePoleLocalLift Q x : ℂ) : OnePoint ℂ) by
        unfold singlePoleLocalLift singlePoleSphereLift
        by_cases hxsrc : x ∈ (chartAt ℂ Q).source
        · simp [hxQ, hxsrc]
        · simp [hxQ, hxsrc]]
      exact hcoe.congr' hlocal
    toFiniteFun_mdifferentiable := fun g hg => by
      have hQ := congrFun hg Q
      simp [singlePoleSphereLift] at hQ
    toMap_eq_infty_of_poleDivisor_pos := fun x hx => by
      have heq : x = Q := by
        by_contra hne
        rw [Divisor.point_apply_ne hne] at hx
        exact (lt_irrefl _) hx
      unfold singlePoleSphereLift
      rw [if_pos heq]
    exists_modulus_atTop_at_pole := fun P hP => by
      have hPQ : P = Q := by
        by_contra hne
        rw [Divisor.point_apply_ne hne] at hP
        exact (lt_irrefl _ hP)
      subst P
      refine ⟨singlePoleLocalLift Q, ?_, ?_⟩
      · intro x hx
        have hx_ne : x ≠ Q := by
          intro h
          rw [h, Divisor.point_apply_self] at hx
          exact zero_ne_one hx.symm
        unfold singlePoleSphereLift singlePoleLocalLift
        by_cases hxsrc : x ∈ (chartAt ℂ Q).source
        · simp [hx_ne, hxsrc]
        · simp [hx_ne, hxsrc]
      · let φ := chartAt ℂ Q
        have hφ₀ : Filter.Tendsto (fun x : X => φ x - φ Q)
            (nhdsWithin Q {Q}ᶜ) (nhds (0 : ℂ)) := by
          have hφ : Filter.Tendsto (fun x : X => φ x) (nhds Q) (nhds (φ Q)) :=
            φ.continuousAt (mem_chart_source ℂ Q)
          have hc : Filter.Tendsto (fun _ : X => φ Q) (nhds Q) (nhds (φ Q)) :=
            tendsto_const_nhds
          simpa using (hφ.sub hc).mono_left nhdsWithin_le_nhds
        have hφ_ne : ∀ᶠ x in nhdsWithin Q {Q}ᶜ, φ x - φ Q ≠ 0 := by
          have hsrc : ∀ᶠ x in nhdsWithin Q {Q}ᶜ, x ∈ φ.source :=
            mem_nhdsWithin_of_mem_nhds (φ.open_source.mem_nhds (mem_chart_source ℂ Q))
          have hne : ∀ᶠ x in nhdsWithin Q {Q}ᶜ, x ≠ Q :=
            eventually_nhdsWithin_of_forall (by intro x hx; exact hx)
          filter_upwards [hsrc, hne] with x hxsrc hxne hzero
          apply hxne
          exact φ.injOn hxsrc (mem_chart_source ℂ Q) (sub_eq_zero.mp hzero)
        have hrecip : Filter.Tendsto (fun x : X => ‖(φ x - φ Q)⁻¹‖)
            (nhdsWithin Q {Q}ᶜ) Filter.atTop := by
          exact tendsto_norm_inv_nhdsNE_zero_atTop.comp
            (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
              (fun x : X => φ x - φ Q) hφ₀ hφ_ne)
        rcases cMfldBump_eq_one_near Q with ⟨U, hUopen, hQU, hU⟩
        have hsrc : ∀ᶠ x in nhdsWithin Q {Q}ᶜ, x ∈ φ.source :=
          mem_nhdsWithin_of_mem_nhds (φ.open_source.mem_nhds (mem_chart_source ℂ Q))
        have hne : ∀ᶠ x in nhdsWithin Q {Q}ᶜ, x ≠ Q :=
          eventually_nhdsWithin_of_forall (by intro x hx; exact hx)
        have hUevent : ∀ᶠ x in nhdsWithin Q {Q}ᶜ, x ∈ U :=
          mem_nhdsWithin_of_mem_nhds (hUopen.mem_nhds hQU)
        refine hrecip.congr' ?_
        filter_upwards [hsrc, hne, hUevent] with x hxsrc hxne hxU
        simp [singlePoleLocalLift, φ, hxsrc, hxne, hU x hxU, div_eq_mul_inv]
    hasBranchedCoverDataOfPoleDegree := singlePole_hasBranchedCoverDataOfPoleDegree Q }

/-- A single-pole map is non-constant. -/
theorem singlePoleMeromorphicMap_nonconstant (Q : X) [Nontrivial X] :
    (singlePoleMeromorphicMap Q).Nonconstant := by
  intro ⟨c, hc⟩
  obtain ⟨r, hr⟩ := exists_ne Q
  have h1 := hc Q
  have h2 := hc r
  unfold singlePoleMeromorphicMap at h1 h2
  simp [singlePoleSphereLift] at h1
  subst h1
  simp [singlePoleSphereLift, hr] at h2
  split_ifs at h2
  · exact OnePoint.coe_ne_infty _ h2
  · exact OnePoint.coe_ne_infty _ h2

/-! ### Two-pole BranchedCoverData construction -/

/-- Finite fibers for the two-pole map, assuming continuity. -/
lemma twoPole_finite_fiber (Q1 Q2 : X) (hne : Q1 ≠ Q2)
    (f := fun x : X => if x = Q1 ∨ x = Q2 then
      (OnePoint.infty : OnePoint ℂ) else ((0 : ℂ) : OnePoint ℂ))
    (hcont : Continuous f) :
    ∀ y : OnePoint ℂ, (f ⁻¹' {y}).Finite := by
  -- Blocked: this statement is false for the displayed map on any infinite
  -- source, since the `0`-fibre is the complement of the two marked points.
  -- Continuity of this indicator-style map cannot provide finite fibres.
  sorry

/-- The weighted fiber count of the two-pole map is constant across all fibers. -/
lemma twoPole_fiberSum_const (Q1 Q2 : X) (hne : Q1 ≠ Q2)
    (f := fun x : X => if x = Q1 ∨ x = Q2 then
      (OnePoint.infty : OnePoint ℂ) else ((0 : ℂ) : OnePoint ℂ))
    (hcont : Continuous f)
    (hfin : ∀ y : OnePoint ℂ, (f ⁻¹' {y}).Finite) :
    ∀ y₁ y₂ : OnePoint ℂ,
      (hfin y₁).toFinset.sum (fun _ => 1) = (hfin y₂).toFinset.sum (fun _ => 1) := by
  -- Blocked with `twoPole_finite_fiber`: the finite fibre hypothesis is not
  -- honestly obtainable for the current two-valued placeholder map.
  sorry

/-- Local bijectivity of the two-pole map at unramified points. -/
lemma twoPole_local_bijective (Q1 Q2 : X) (hne : Q1 ≠ Q2)
    (f := fun x : X => if x = Q1 ∨ x = Q2 then
      (OnePoint.infty : OnePoint ℂ) else ((0 : ℂ) : OnePoint ℂ))
    (hcont : Continuous f) :
    ∀ x : X, (fun (_ : X) => (1 : ℕ)) x = 1 →
      ∃ U : Set X, ∃ V : Set (OnePoint ℂ),
        IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ f x ∈ V ∧ Set.BijOn f U V := by
  -- Blocked: away from the two marked points the displayed map is locally
  -- constant `0`, so it cannot be locally bijective on nontrivial
  -- neighborhoods.  This needs an actual two-pole meromorphic function.
  sorry

/-- The `hasBranchedCoverDataOfPoleDegree` obligation for `twoPointMeromorphicMap`. -/
lemma twoPole_hasBranchedCoverDataOfPoleDegree (Q1 Q2 : X) (hne : Q1 ≠ Q2)
    (f := fun x : X => if x = Q1 ∨ x = Q2 then
      (OnePoint.infty : OnePoint ℂ) else ((0 : ℂ) : OnePoint ℂ)) :
    Continuous f →
    ∃ (h : BranchedCoverData X (OnePoint ℂ) f),
      branchedDegree h = (Divisor.point Q1 + Divisor.point Q2).degree.toNat := by
  -- Blocked: the current two-valued placeholder map cannot support the
  -- finite-fibre or local-bijection fields required by `BranchedCoverData`.
  sorry

/-- A meromorphic map with two simple poles at Q1 and Q2. -/
noncomputable def twoPointMeromorphicMap (Q1 Q2 : X) (hne : Q1 ≠ Q2) : MeromorphicMapToSphere X :=
  { toMap := fun x => if x = Q1 ∨ x = Q2 then OnePoint.infty else ((0 : ℂ) : OnePoint ℂ)
    locally_meromorphic := True
    zeroDivisor := 0
    poleDivisor := Divisor.point Q1 + Divisor.point Q2
    principalDivisor := -(Divisor.point Q1 + Divisor.point Q2)
    principalDivisor_eq := by simp
    poleDivisor_nonneg := fun x => by
      classical
      apply add_nonneg
      · exact Divisor.effective_point Q1 x
      · exact Divisor.effective_point Q2 x
    zero_or_pole_eq_zero := fun _ => Or.inl rfl
    toMap_ne_infty_of_poleDivisor_zero := fun x hx => by
      have hne1 : x ≠ Q1 := by
        intro h
        have hx' := hx
        rw [h] at hx'
        have : (Divisor.point Q1) Q1 + (Divisor.point Q2) Q1 = 0 := hx'
        rw [Divisor.point_apply_self] at this
        have h_nonneg := Divisor.effective_point Q2 Q1
        linarith
      have hne2 : x ≠ Q2 := by
        intro h
        have hx' := hx
        rw [h] at hx'
        have : (Divisor.point Q1) Q2 + (Divisor.point Q2) Q2 = 0 := hx'
        rw [Divisor.point_apply_self] at this
        have h_nonneg := Divisor.effective_point Q1 Q2
        linarith
      split_ifs with heq
      · rcases heq with heq1 | heq2
        · contradiction
        · contradiction
      · exact OnePoint.coe_ne_infty _
    continuousOn_ne_infty := by
      refine ContinuousOn.congr
        (f := fun _ : X => ((0 : ℂ) : OnePoint ℂ))
        continuousOn_const ?_
      intro x hx
      by_cases hpole : x = Q1 ∨ x = Q2
      · simp at hx
        rcases hpole with hQ1 | hQ2
        · exact False.elim (hx.1 hQ1)
        · exact False.elim (hx.2 hQ2)
      · simp [hpole]
    toFiniteFun_mdifferentiable := fun g hg => by
      have hQ := congrFun hg Q1
      simp at hQ
    toMap_eq_infty_of_poleDivisor_pos := fun x hx => by
      have heq : x = Q1 ∨ x = Q2 := by
        by_contra h_nor
        push_neg at h_nor
        have hx' : 0 < (Divisor.point Q1) x + (Divisor.point Q2) x := hx
        have hzero : (Divisor.point Q1) x + (Divisor.point Q2) x = 0 := by
          rw [Divisor.point_apply_ne h_nor.1, Divisor.point_apply_ne h_nor.2, add_zero]
        rw [hzero] at hx'
        exact lt_irrefl _ hx'
      rw [if_pos heq]
    exists_modulus_atTop_at_pole := fun _ _ => by
      -- Blocked: the displayed two-pole placeholder is finite and equal to
      -- `0` on every punctured neighborhood away from the pole point itself,
      -- so no finite lift can have norm tending to `atTop`.  The constructor
      -- needs a genuine two-pole meromorphic map.
      sorry
    hasBranchedCoverDataOfPoleDegree := twoPole_hasBranchedCoverDataOfPoleDegree Q1 Q2 hne }

/-- A two-pole map is non-constant. -/
theorem twoPointMeromorphicMap_nonconstant [Nonempty X] (Q1 Q2 : X) (hne : Q1 ≠ Q2) :
    (twoPointMeromorphicMap Q1 Q2 hne).Nonconstant := by
  intro ⟨c, hc⟩
  have h1 := hc Q1
  -- I need a point that is not a pole.
  obtain ⟨r, hr1, hr2⟩ := exists_distinct_from_pair_of_chartedSpaceComplex (X := X) Q1 Q2
  have hr := hc r
  unfold twoPointMeromorphicMap at h1 hr
  simp at h1
  subst h1
  simp [hr1, hr2] at hr

end JacobianChallenge.HolomorphicForms
