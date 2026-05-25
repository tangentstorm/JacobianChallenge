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

/--
f(x) = cMfldBump(Q,x) / ((chartAt ℂ Q).toFun(x) - φ(Q))  on chart, 0 off,
    with f(Q) := ∞.
-/
noncomputable def singlePoleSphereLift (Q : X) (x : X) : OnePoint ℂ :=
  if x = Q then
    OnePoint.infty
  else if x ∈ (chartAt ℂ Q).source then
    let φ := chartAt ℂ Q
    let val : ℂ := (cMfldBump Q x : ℝ) / (φ x - φ Q)
    (val : OnePoint ℂ)
  else
    ((0 : ℂ) : OnePoint ℂ)

/--
Local complex-valued lift for the single-pole function, used in the
modulus-divergence axiom.
-/
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

/-!
### Honest prescribed-pole data versus scaffold maps

The displayed maps below are local scaffolding: `singlePoleSphereLift` is cut
off by a bump function and the two-pole map is an indicator-style function.
Neither displayed map can honestly support finite-fiber, weighted-fiber
constancy, or local-bijectivity statements.  In particular, their `0`-fibers
can be large and they are locally constant on nontrivial regions.

The downstream mathematical API should consume one of the bundled data records
below when it needs the analytic content of an honest meromorphic map with
prescribed pole divisor.
-/

/--
Bundled data for an honest meromorphic map with one prescribed simple
pole, *without* a `BranchedCoverDataOfPoleDegree` field. Branch data
is a *proved consequence* of the fields below
(via `genusZero_fixedPole_branchedCoverDataOfPoleDegree` /
`MeromorphicMapToSphere.branchedCoverDataOfPoleDegree_of_simple_pole`),
so it does not belong as an assumed field.
-/
structure SinglePoleMeromorphicAnalyticData (Q : X) where
  map : MeromorphicMapToSphere X
  poleDivisor_eq : map.poles = Divisor.point Q
  nonconstant : map.Nonconstant
  poleModulusData : map.PoleModulusData
  analyticData : map.AnalyticData

/--
Bundled data for an honest meromorphic map with one prescribed simple
pole.  The cutoff formula `singlePoleSphereLift` is not used to prove these
fields; future constructors should fill this record from Riemann-Roch or a
global meromorphic-function construction.

The `analyticData` field carries the per-point chart-local Laurent /
order content that the abstract `MeromorphicMapToSphere` interface cannot
derive — the genuine analytic content of the map.

The `branchedCoverDataOfPoleDegree` field is a *proved consequence* of
the other fields (see
`MeromorphicMapToSphere.branchedCoverDataOfPoleDegree_of_simple_pole`),
retained here as cached data for downstream consumers.
-/
structure SinglePoleMeromorphicMapData (Q : X) where
  map : MeromorphicMapToSphere X
  poleDivisor_eq : map.poles = Divisor.point Q
  nonconstant : map.Nonconstant
  poleModulusData : map.PoleModulusData
  analyticData : map.AnalyticData
  branchedCoverDataOfPoleDegree : map.BranchedCoverDataOfPoleDegree

/--
The `analyticData` field carries the per-point chart-local Laurent /
order content that the abstract `MeromorphicMapToSphere` interface cannot
derive — the genuine analytic content of the map.
-/
structure TwoPointMeromorphicMapData (Q1 Q2 : X) where
  map : MeromorphicMapToSphere X
  poleDivisor_eq : map.poles = Divisor.point Q1 + Divisor.point Q2
  nonconstant : map.Nonconstant
  poleModulusData : map.PoleModulusData
  analyticData : map.AnalyticData
  branchedCoverDataOfPoleDegree : map.BranchedCoverDataOfPoleDegree

/--
Scaffold constructor for the displayed single-pole cutoff map.

This constructor assigns `poleDivisor := Divisor.point Q` directly, so it is
not an analytic route theorem. Production simple-pole conclusions should use
the honest bundled record `SinglePoleMeromorphicMapData` or an order-to-divisor
bridge — see `meromorphicMapToSphere_of_inverse_order_one_frontier` in
`HarmonicFunctions.lean`.
-/
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

/-- Helper: `‖1/z‖ → ∞` as `z → 0` within `{0}ᶜ` in `ℂ`. -/
private theorem norm_inv_tendsto_atTop_at_zero :
    Filter.Tendsto (fun z : ℂ => ‖(1 : ℂ) / z‖)
      (nhdsWithin 0 {0}ᶜ) Filter.atTop := by
  have hrw : (fun z : ℂ => ‖(1 : ℂ) / z‖) = fun z => (‖z‖)⁻¹ := by
    ext z; rw [one_div, norm_inv]
  rw [hrw]
  have hnorm_tendsto :
      Filter.Tendsto (fun z : ℂ => ‖z‖) (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h0 : ‖(0 : ℂ)‖ = 0 := norm_zero
      have hc : Filter.Tendsto (norm : ℂ → ℝ) (nhds 0) (nhds (‖(0 : ℂ)‖)) :=
        (continuous_norm : Continuous (norm : ℂ → ℝ)).tendsto 0
      rw [h0] at hc
      exact Filter.Tendsto.mono_left hc nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      rw [Set.mem_Ioi, norm_pos_iff]
      exact hz
  exact Filter.Tendsto.comp tendsto_inv_nhdsGT_zero hnorm_tendsto

omit [T2Space X] [IsManifold (𝓘(ℂ, ℂ)) ⊤ X] [Periods.StableChartAt ℂ X] in
/--
Modulus divergence at `Q` for the cutoff lift.

The scaffold's `singlePoleSphereLift` agrees with `singlePoleLocalLift Q`
near `Q` (the bump cutoff is `1` on a neighborhood of `Q`), and the local
lift is `1/(chartAt ℂ Q x - chartAt ℂ Q Q)` there. The chart map sends `Q`
to its image and is injective on its source, so the denominator tends to
`0` (but is nonzero off `Q`), hence the modulus tends to `+∞`.
-/
private theorem singlePoleLocalLift_norm_tendsto_atTop (Q : X) :
    Filter.Tendsto (fun x => ‖singlePoleLocalLift Q x‖)
      (nhdsWithin Q {Q}ᶜ) Filter.atTop := by
  -- Pick an open neighborhood `U` of `Q` on which the bump equals `1`.
  obtain ⟨U, hUopen, hQU, hUbump⟩ := cMfldBump_eq_one_near (X := X) Q
  -- Combine with chart source: there is an open set `W ⊆ U ∩ source` containing `Q`.
  set W : Set X := U ∩ (chartAt ℂ Q).source with hW_def
  have hWopen : IsOpen W := hUopen.inter (chartAt ℂ Q).open_source
  have hQW : Q ∈ W := ⟨hQU, mem_chart_source ℂ Q⟩
  -- For `x ∈ W` with `x ≠ Q`, `singlePoleLocalLift Q x = 1 / (φ x - φ Q)`.
  set φ : X → ℂ := fun x => chartAt ℂ Q x with hφ_def
  have hlocal_eq : ∀ᶠ x in nhdsWithin Q {Q}ᶜ,
      singlePoleLocalLift Q x = 1 / (φ x - φ Q) := by
    refine eventually_nhdsWithin_iff.mpr (Filter.Eventually.mono
      (hWopen.mem_nhds hQW) ?_)
    intro x hxW hxQ
    have hxQ' : x ≠ Q := hxQ
    have hbump : cMfldBump Q x = 1 := hUbump x hxW.1
    have hxsrc : x ∈ (chartAt ℂ Q).source := hxW.2
    unfold singlePoleLocalLift
    simp [hxsrc, hxQ', hbump, hφ_def, one_div]
  -- It now suffices to show `‖1 / (φ x - φ Q)‖ → ∞` along `nhdsWithin Q {Q}ᶜ`.
  have hsuffices :
      Filter.Tendsto (fun x => ‖(1 : ℂ) / (φ x - φ Q)‖)
        (nhdsWithin Q {Q}ᶜ) Filter.atTop := by
    -- Push `φ` to the limit: as `x → Q`, `φ x → φ Q`, so `φ x - φ Q → 0`.
    -- Plus injectivity of `φ` on source gives `φ x - φ Q ≠ 0` for `x ≠ Q` in source.
    have hφ_cont : ContinuousAt φ Q :=
      (chartAt ℂ Q).continuousAt (mem_chart_source ℂ Q)
    have hφ_tendsto : Filter.Tendsto (fun x => φ x - φ Q) (nhds Q) (nhds 0) := by
      have h₁ : Filter.Tendsto φ (nhds Q) (nhds (φ Q)) := hφ_cont
      have h₂ := h₁.sub_const (φ Q)
      simpa using h₂
    have hφ_within : Filter.Tendsto (fun x => φ x - φ Q) (nhdsWithin Q {Q}ᶜ) (nhds 0) :=
      hφ_tendsto.mono_left nhdsWithin_le_nhds
    have hne_ev : ∀ᶠ x in nhdsWithin Q {Q}ᶜ, (φ x - φ Q) ≠ 0 := by
      refine eventually_nhdsWithin_iff.mpr (Filter.Eventually.mono
        ((chartAt ℂ Q).open_source.mem_nhds (mem_chart_source ℂ Q)) ?_)
      intro x hxsrc hxQ
      have hxQ' : x ≠ Q := hxQ
      intro h
      apply hxQ'
      exact (chartAt ℂ Q).injOn hxsrc (mem_chart_source ℂ Q) (sub_eq_zero.mp h)
    have hφ_within_cmpl :
        Filter.Tendsto (fun x => φ x - φ Q) (nhdsWithin Q {Q}ᶜ) (nhdsWithin 0 {0}ᶜ) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hφ_within hne_ev
    -- Compose with `‖1/·‖ → ∞` at `0`.
    exact norm_inv_tendsto_atTop_at_zero.comp hφ_within_cmpl
  -- Replace `singlePoleLocalLift Q x` by `1 / (φ x - φ Q)` eventually.
  refine hsuffices.congr' ?_
  filter_upwards [hlocal_eq] with x hx
  show (fun x => ‖(1 : ℂ) / (φ x - φ Q)‖) x = (fun x => ‖singlePoleLocalLift Q x‖) x
  simp only
  rw [hx]

omit [Periods.StableChartAt ℂ X] in
/--
The scaffold `singlePoleMeromorphicMap Q` satisfies `PoleModulusData`.

The bump cutoff in `singlePoleSphereLift` does not interfere with the
modulus-divergence content of `PoleModulusData`: the cutoff equals `1` on
a neighborhood of `Q`, so locally `1/(z - z₀)` is the unbumped principal
part, and its modulus diverges. The same `singlePoleLocalLift Q` that
appears in the scaffold's `continuousOn_ne_infty` field also serves as
the witness `g` for the modulus-data field.

This shows that `PoleModulusData` by itself is **not** the missing
analytic content for genus-zero classification. The actually unprovable
piece for the scaffold is `BranchedCoverDataOfPoleDegree`: the cutoff
produces a (possibly infinite) constant-zero region outside the chart
source, so the `0`-fiber is too large to satisfy `finite_fiber`, and the
weighted-fiber-constancy field of `BranchedCoverData` fails. Compare
with `SinglePoleMeromorphicMapData`, which is the honest bundled record
requiring both pieces of route data.
-/
theorem singlePoleMeromorphicMap_poleModulusData (Q : X) :
    (singlePoleMeromorphicMap Q).PoleModulusData where
  exists_modulus_atTop_at_pole := by
    classical
    intro P hP
    -- Only `P = Q` has positive `poleDivisor` for the scaffold.
    have hPQ : P = Q := by
      by_contra hPneQ
      have hzero : (singlePoleMeromorphicMap Q).poleDivisor P = 0 := by
        change (Divisor.point Q) P = 0
        exact Divisor.point_apply_ne hPneQ
      rw [hzero] at hP
      exact (lt_irrefl _) hP
    refine ⟨singlePoleLocalLift Q, ?_, ?_⟩
    · -- For x with poleDivisor x = 0 (i.e. x ≠ Q), `toMap x = (singlePoleLocalLift Q x : OnePoint ℂ)`.
      intro x hx
      have hxQ : x ≠ Q := by
        intro h
        rw [h] at hx
        have hval : (singlePoleMeromorphicMap Q).poleDivisor Q = 1 := by
          change (Divisor.point Q : Divisor X) Q = 1
          exact Divisor.point_apply_self (X := X) Q
        rw [hval] at hx
        exact one_ne_zero hx
      -- Unfold both sides and case-split on chart membership.
      show singlePoleSphereLift Q x = ((singlePoleLocalLift Q x : ℂ) : OnePoint ℂ)
      unfold singlePoleSphereLift singlePoleLocalLift
      by_cases hxsrc : x ∈ (chartAt ℂ Q).source
      · simp [hxQ, hxsrc]
      · simp [hxQ, hxsrc]
    · -- Modulus divergence: rewrite the filter at `P` to be `Q`-indexed.
      rw [hPQ]
      exact singlePoleLocalLift_norm_tendsto_atTop Q

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

/--
Scaffold constructor for the displayed two-point indicator map.

This constructor prescribes its pole divisor directly and is isolated as
scaffolding, not as a proof that analytic order data creates those poles.

**Asymmetry with the single-pole scaffold.** Unlike
`singlePoleMeromorphicMap`, this indicator scaffold genuinely fails
`PoleModulusData`. The reason: `toMap x = (0 : OnePoint ℂ)` for all
`x ≠ Q1, Q2`, so the modulus-data witness `g` would be forced to satisfy
`g x = 0` on the entire non-pole locus (from
`f.poleDivisor x = 0 → toMap x = (g x : OnePoint ℂ)`). But then `‖g x‖ = 0`
near each pole, contradicting `Tendsto (fun x => ‖g x‖) (nhdsWithin Qᵢ {Qᵢ}ᶜ)
atTop`. So this scaffold cannot be promoted to `PoleModulusData` even in
the weakened sense satisfied by the single-pole bump map.
-/
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

omit [Periods.StableChartAt ℂ X] in
/--
The two-point indicator scaffold genuinely fails `PoleModulusData`.

Any candidate witness `g` for `exists_modulus_atTop_at_pole` at `Q1` must
satisfy `(twoPointMeromorphicMap Q1 Q2 hne).toMap x = (g x : OnePoint ℂ)`
whenever `poleDivisor x = 0` (i.e. `x ≠ Q1, Q2`). But `toMap x = 0` on that
locus by construction, so `g x = 0` for all `x ≠ Q1, Q2`. Combining
`Tendsto (fun x => ‖g x‖) (𝓝[{Q1}ᶜ] Q1) atTop` (for `N = 1`) with
`g x = 0` on the punctured-Q2 neighborhood of Q1 (which by `T1Space`
contains a punctured neighborhood of Q1) yields an eventually-false
statement, forcing `𝓝[{Q1}ᶜ] Q1 = ⊥`. That is equivalent to `{Q1}` being
open in `X`, which contradicts the chart map continuity into ℂ (where
singletons are not open).

This formal asymmetry-witnessing theorem reinforces the project boundary:
`PoleModulusData` IS analytically substantive for some maps (the
two-point indicator cannot satisfy it), even though weaker bump scaffolds
like `singlePoleMeromorphicMap` can. The genuinely missing piece for
genus-zero classification remains `BranchedCoverDataOfPoleDegree`.
-/
theorem twoPointMeromorphicMap_not_poleModulusData
    (Q1 Q2 : X) (hne : Q1 ≠ Q2) :
    ¬ (twoPointMeromorphicMap Q1 Q2 hne).PoleModulusData := by
  classical
  intro hmod
  -- Pole positivity at Q1.
  have hQ1_pos : 0 < (twoPointMeromorphicMap Q1 Q2 hne).poleDivisor Q1 := by
    show 0 < (Divisor.point Q1 + Divisor.point Q2 : Divisor X) Q1
    have h1 : (Divisor.point Q1 : Divisor X) Q1 = 1 :=
      Divisor.point_apply_self (X := X) Q1
    have h2 : (Divisor.point Q2 : Divisor X) Q1 = 0 :=
      Divisor.point_apply_ne hne
    rw [Finsupp.add_apply, h1, h2]
    decide
  -- Get a witness.
  obtain ⟨g, hg_eq, hg_div⟩ := hmod.exists_modulus_atTop_at_pole Q1 hQ1_pos
  -- For x ≠ Q1, Q2 we have toMap x = 0 (the finite value), so g x = 0.
  have hg_zero_off : ∀ x : X, x ≠ Q1 → x ≠ Q2 → g x = 0 := by
    intro x hx1 hx2
    have hpole : (twoPointMeromorphicMap Q1 Q2 hne).poleDivisor x = 0 := by
      show (Divisor.point Q1 + Divisor.point Q2 : Divisor X) x = 0
      rw [Finsupp.add_apply, Divisor.point_apply_ne hx1, Divisor.point_apply_ne hx2]
      decide
    have hval : (twoPointMeromorphicMap Q1 Q2 hne).toMap x =
        ((g x : ℂ) : OnePoint ℂ) := hg_eq x hpole
    have htoMap : (twoPointMeromorphicMap Q1 Q2 hne).toMap x = ((0 : ℂ) : OnePoint ℂ) := by
      show (if x = Q1 ∨ x = Q2 then OnePoint.infty else ((0 : ℂ) : OnePoint ℂ)) =
        ((0 : ℂ) : OnePoint ℂ)
      simp [hx1, hx2]
    have hcoe : ((g x : ℂ) : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ) := by
      rw [← hval, htoMap]
    exact OnePoint.coe_injective hcoe
  -- `{Q2}ᶜ` is a neighborhood of Q1 (T1Space).
  have hQ2_in_nhds : ({Q2}ᶜ : Set X) ∈ nhds Q1 :=
    isOpen_compl_singleton.mem_nhds hne
  -- Eventually in `𝓝[{Q1}ᶜ] Q1`, `‖g x‖ = 0`.
  have h_zero_ev : ∀ᶠ x in nhdsWithin Q1 ({Q1}ᶜ : Set X), ‖g x‖ = 0 := by
    refine eventually_nhdsWithin_iff.mpr ?_
    filter_upwards [hQ2_in_nhds] with x hxQ2 hxQ1
    rw [hg_zero_off x hxQ1 hxQ2, norm_zero]
  -- Eventually in the same filter, `‖g x‖ ≥ 1` (from `atTop`).
  have h_ge_ev : ∀ᶠ x in nhdsWithin Q1 ({Q1}ᶜ : Set X), (1 : ℝ) ≤ ‖g x‖ :=
    hg_div (Filter.eventually_ge_atTop 1)
  -- Combine to force the filter to be `⊥`.
  have h_bot : (nhdsWithin Q1 ({Q1}ᶜ : Set X)) = ⊥ := by
    have hfalse : ∀ᶠ _x in nhdsWithin Q1 ({Q1}ᶜ : Set X), False := by
      filter_upwards [h_zero_ev, h_ge_ev] with x hx0 hx1
      rw [hx0] at hx1
      linarith
    rwa [Filter.eventually_false_iff_eq_bot] at hfalse
  -- So `{Q1}` would be open in X. Pull back through chart to get a contradiction.
  have hQ1_open : IsOpen ({Q1} : Set X) := by
    rw [isOpen_singleton_iff_punctured_nhds]
    exact h_bot
  -- `chartAt ℂ Q1` is an `OpenPartialHomeomorph`: it maps `{Q1}` injectively into
  -- ℂ. If `{Q1}` is open, its chart image is open in ℂ (a singleton), which is
  -- impossible since ℂ has no isolated points.
  have hQ1_open_inter : IsOpen ({Q1} ∩ (chartAt ℂ Q1).source : Set X) :=
    hQ1_open.inter (chartAt ℂ Q1).open_source
  have hsubset : ({Q1} ∩ (chartAt ℂ Q1).source : Set X) ⊆ (chartAt ℂ Q1).source :=
    Set.inter_subset_right
  have hQ1_image_open : IsOpen ((chartAt ℂ Q1) '' ({Q1} ∩ (chartAt ℂ Q1).source)) :=
    (chartAt ℂ Q1).isOpen_image_of_subset_source hQ1_open_inter hsubset
  have hQ1_image_eq : (chartAt ℂ Q1) '' ({Q1} ∩ (chartAt ℂ Q1).source) =
      {chartAt ℂ Q1 Q1} := by
    ext z
    simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, ⟨hxQ1, _⟩, rfl⟩; exact hxQ1 ▸ rfl
    · rintro rfl; exact ⟨Q1, ⟨rfl, mem_chart_source ℂ Q1⟩, rfl⟩
  rw [hQ1_image_eq] at hQ1_image_open
  -- Singletons in ℂ are not open.
  have : ¬ IsOpen ({chartAt ℂ Q1 Q1} : Set ℂ) := by
    rw [isOpen_singleton_iff_punctured_nhds]
    intro hbot
    exact (PerfectSpace.not_isolated (X := ℂ) (chartAt ℂ Q1 Q1)).ne hbot
  exact this hQ1_image_open

end JacobianChallenge.HolomorphicForms
