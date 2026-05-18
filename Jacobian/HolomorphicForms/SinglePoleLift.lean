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

/-! ### Honest prescribed-pole data versus scaffold maps

The displayed maps below are local scaffolding: `singlePoleSphereLift` is cut
off by a bump function and the two-pole map is an indicator-style function.
Neither displayed map can honestly support finite-fiber, weighted-fiber
constancy, or local-bijectivity statements.  In particular, their `0`-fibers
can be large and they are locally constant on nontrivial regions.

The downstream mathematical API should consume one of the bundled data records
below when it needs the analytic content of an honest meromorphic map with
prescribed pole divisor. -/

/-- Bundled data for an honest meromorphic map with one prescribed simple
pole.  The cutoff formula `singlePoleSphereLift` is not used to prove these
fields; future constructors should fill this record from Riemann-Roch or a
global meromorphic-function construction. -/
structure SinglePoleMeromorphicMapData (Q : X) where
  map : MeromorphicMapToSphere X
  poleDivisor_eq : map.poles = Divisor.point Q
  nonconstant : map.Nonconstant
  poleModulusData : map.PoleModulusData
  branchedCoverDataOfPoleDegree : map.BranchedCoverDataOfPoleDegree

/-- Bundled data for an honest meromorphic map with two prescribed simple
poles.  This replaces the former false branched-cover claims about the
two-valued indicator placeholder. -/
structure TwoPointMeromorphicMapData (Q1 Q2 : X) where
  map : MeromorphicMapToSphere X
  poleDivisor_eq : map.poles = Divisor.point Q1 + Divisor.point Q2
  nonconstant : map.Nonconstant
  poleModulusData : map.PoleModulusData
  branchedCoverDataOfPoleDegree : map.BranchedCoverDataOfPoleDegree

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
  }

omit [JacobianChallenge.Periods.StableChartAt ℂ X] in
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

/-- A meromorphic map with two simple poles at Q1 and Q2. -/
noncomputable def twoPointMeromorphicMap (Q1 Q2 : X) (_hne : Q1 ≠ Q2) :
    MeromorphicMapToSphere X :=
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
  }

omit [T2Space X] [JacobianChallenge.Periods.StableChartAt ℂ X] in
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
