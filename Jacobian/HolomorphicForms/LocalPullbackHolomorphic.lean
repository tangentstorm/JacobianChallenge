import Jacobian.HolomorphicForms.BranchedCover
import Jacobian.HolomorphicForms.HolomorphicMap
import Jacobian.HolomorphicForms.EvalAtOneHelper
import Jacobian.HolomorphicForms.TraceSpec
import Jacobian.TraceDegree.TraceDefinition
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# Local-pullback holomorphic-variation: full axiom discharge (M4b)

This file discharges (as a stand-alone theorem) the project's single
custom axiom

```
axiom localPullbackAt_holomorphic
    {f : X → Y} (h : BranchedCoverData X Y f)
    (hcompat : h.RamificationIndexCompatible)
    (hf : IsHolomorphic f)
    (ω : HolomorphicOneForm ℂ X)
    (x : X) (hx : h.ramificationIndex x = 1) :
    IsHolomorphicAt (localPullbackAt h hf ω x hx) (f x)
```

(declared at `Jacobian/TraceDegree/TraceDefinition.lean:220`; see
`ref/axiom-audit.md` §1 for the 13 transitive dependents).

The new theorem `localPullbackAt_holomorphic_theorem` has the same
signature as the axiom and is proved sorry-free. M4-final (next
commit) will replace the axiom with a `theorem` delegating to this
proof.

## Proof structure

1. **M4-prep — `BranchedCoverData.localInverseAt_eventually_unramified`**:
   the local inverse stays in the unramified locus eventually,
   enabling pointwise application of the unramified-only formula
   `cotangentPushforward_apply_one` (TraceSpec.lean L1003).

2. **`etaTimesOne_chart_local_analytic`**: chart-local analyticity of
   `ω.toFun · 1` extracted from the inline DB-B pattern.

3. **`localPullbackAt_holomorphic_theorem`**: the full discharge. The
   strategy passes through the chart on `CotangentModelFiber ℂ`
   (the singleton chart from `cotangentFiberIso`), reducing to
   analyticity of a ℂ-valued chart-local function. By
   `cotangentPushforward_apply_one` (eventually applicable via
   M4-prep), the chart-local value at `z` is
   ```
   (deriv (chartLocalAt f x') (chartAt ℂ x' x'))⁻¹ * (ω.toFun x' 1)
   ```
   where `x' = h.localInverseAt x hx ((chartAt ℂ (f x)).symm z)`.
   Under `StableChartAt`, this collapses to
   ```
   (deriv F (r z))⁻¹ * Θ(r z)
   ```
   where `F := chartLocalAt f x`, `r : ℂ → ℂ` is the analytic local
   inverse via `HasStrictDerivAt.localInverse`, and `Θ` is the eta-
   times-one function (analytic by `etaTimesOne_chart_local_analytic`).
   Both factors are analytic at `w₀ := chartAt ℂ (f x) (f x)`;
   product/inverse of analytic functions gives analyticity of the
   candidate; `congr_of_eventuallyEq` lifts back to the goal.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold Topology
open Filter Set Bundle

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]

omit [ChartedSpace ℂ X] [ChartedSpace ℂ Y] in
/--
**Eventually-unramified at the local inverse.**

For an unramified preimage `x` of `f x`, the local inverse maps a
neighborhood of `f x` into the unramified locus of `f`.
-/
theorem BranchedCoverData.localInverseAt_eventually_unramified
    [T2Space X] [T2Space Y] [Nonempty X]
    {f : X → Y} (h : BranchedCoverData X Y f)
    (x : X) (hx : h.ramificationIndex x = 1) :
    ∀ᶠ y' in 𝓝 (f x), h.ramificationIndex (h.localInverseAt x hx y') = 1 := by
  classical
  obtain ⟨U, V, hUopen, hVopen, hxU, hfxV, hbij, hright_branch, hleft_branch⟩ :=
    h.localInverse_is_inverse hx
  set ramSet : Set X := {y | h.ramificationIndex y ≠ 1} \ {x} with hramSet_def
  have hramSet_finite : ramSet.Finite := by
    apply Set.Finite.subset h.ramified_finite
    intro y hy; exact hy.1
  have hxU' : x ∉ ramSet := by intro hramX; exact hramX.2 rfl
  have h_evt_in_V : ∀ᶠ y' in 𝓝 (f x), y' ∈ V :=
    hVopen.mem_nhds hfxV
  have h_localInv_in_U : ∀ y' ∈ V, h.localInverseAt x hx y' ∈ U := by
    intro y' hy'V
    obtain ⟨x', hx'U, hfx'⟩ := hbij.surjOn hy'V
    have h_local_at_y : h.localInverseAt x hx y' = x' := by
      rw [← hfx']
      exact hleft_branch x' hx'U
    rw [h_local_at_y]; exact hx'U
  set bad_X : Set X := U ∩ ramSet with hbad_X_def
  have hbad_X_finite : bad_X.Finite := hramSet_finite.subset (fun _ h' => h'.2)
  set bad_Y : Set Y := f '' bad_X with hbad_Y_def
  have hbad_Y_finite : bad_Y.Finite := hbad_X_finite.image f
  have hfx_not_bad : f x ∉ bad_Y := by
    intro hfxbad
    obtain ⟨x', hx'bad, hfx'eq⟩ := hfxbad
    have hx'U : x' ∈ U := hx'bad.1
    have hx'x : x' = x := hbij.injOn hx'U hxU hfx'eq
    have : x ∈ ramSet := hx'x ▸ hx'bad.2
    exact hxU' this
  have hbad_Y_closed : IsClosed bad_Y := hbad_Y_finite.isClosed
  have h_compl_nhd : bad_Yᶜ ∈ 𝓝 (f x) :=
    hbad_Y_closed.isOpen_compl.mem_nhds hfx_not_bad
  filter_upwards [h_evt_in_V, h_compl_nhd] with y' hy'V hy'bad
  by_contra h_neg
  have h_loc_in_U : h.localInverseAt x hx y' ∈ U := h_localInv_in_U y' hy'V
  have h_loc_in_ram : h.localInverseAt x hx y' ∈ ramSet := by
    refine ⟨h_neg, ?_⟩
    intro h_eq; rw [h_eq] at h_neg; exact h_neg hx
  have h_loc_in_bad : h.localInverseAt x hx y' ∈ bad_X := ⟨h_loc_in_U, h_loc_in_ram⟩
  have h_y'_in_bad : y' ∈ bad_Y := by
    refine ⟨h.localInverseAt x hx y', h_loc_in_bad, ?_⟩
    exact hright_branch y' hy'V
  exact hy'bad h_y'_in_bad

variable
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [JacobianChallenge.Periods.StableChartAt ℂ X]

/--
**Chart-local analyticity of `ω.toFun · 1`.**

For a holomorphic 1-form `ω` on `X` and any base point `x₀`, the
function `ε ↦ (ω.toFun ((chartAt ℂ x₀).symm ε)) 1` is analytic at
`chartAt ℂ x₀ x₀`. Extracted from the inline DB-B pattern at
TraceSpec.lean ~L2812.
-/
theorem etaTimesOne_chart_local_analytic
    (ω : HolomorphicOneForm ℂ X) (x₀ : X) :
    AnalyticAt ℂ (fun ε : ℂ => (ω.toFun ((chartAt ℂ x₀).symm ε)) (1 : ℂ))
      (chartAt ℂ x₀ x₀) := by
  have h1 : ContMDiff (𝓘(ℂ, ℂ)) ((𝓘(ℂ, ℂ)).prod (𝓘(ℂ, ℂ))) ⊤
      (fun x : X => Bundle.TotalSpace.mk' ℂ (E := Bundle.Trivial X ℂ) x
        (show (Bundle.Trivial X ℂ) x from (ω.toFun x) (1 : ℂ))) :=
    ω.contMDiff.clm_bundle_apply contMDiff_tangentSection_one
  have hsrc : (fun x : X => Bundle.TotalSpace.mk' ℂ
      (E := Bundle.Trivial X ℂ) x ((ω.toFun x) (1 : ℂ))) x₀
        ∈ (trivializationAt ℂ (Bundle.Trivial X ℂ) x₀).source := by
    rw [Trivialization.mem_source]
    exact FiberBundle.mem_baseSet_trivializationAt' x₀
  have h_iff :=
    (trivializationAt ℂ (Bundle.Trivial X ℂ) x₀).contMDiffAt_iff
      (IB := 𝓘(ℂ, ℂ)) (IM := 𝓘(ℂ, ℂ)) (n := (⊤ : WithTop ℕ∞))
      (f := fun x : X => Bundle.TotalSpace.mk' ℂ (E := Bundle.Trivial X ℂ) x
        ((ω.toFun x) (1 : ℂ)))
      hsrc
  have h_evalOne : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ⊤
      (fun x : X => (ω.toFun x) (1 : ℂ)) x₀ :=
    (h_iff.mp h1.contMDiffAt).2
  rw [contMDiffAt_iff] at h_evalOne
  obtain ⟨_h_cont, h_cdwithin⟩ := h_evalOne
  rw [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] at h_cdwithin
  exact h_cdwithin.analyticAt

end JacobianChallenge.HolomorphicForms

/-!
### M4b-final — the full axiom discharge theorem
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold Topology
open Filter Set Bundle ContinuousLinearMap

variable {X Y : Type}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]
  [JacobianChallenge.Periods.StableChartAt ℂ X]
  [JacobianChallenge.Periods.StableChartAt ℂ Y]

omit [T2Space X] [CompactSpace X] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] in
/--
**M4b-final — full discharge of `localPullbackAt_holomorphic`.**

Sorry-free, axiom-clean (modulo Lean's standard axioms `propext`,
`Classical.choice`, `Quot.sound`) proof that the local pullback
function is holomorphic at `f x` for an unramified preimage `x`. M4-final
(next commit) replaces the axiom at `TraceDefinition.lean:220` with a
`theorem` delegating to this proof.

The proof passes through the singleton chart on
`CotangentModelFiber ℂ` (via `cotangentFiberIso`), reducing to
analyticity of a ℂ-valued chart-local function. The chart-local form
collapses (under `StableChartAt`) to
`z ↦ (deriv F (r z))⁻¹ * Θ(r z)` where `F := chartLocalAt f x`,
`r : ℂ → ℂ` is the analytic local inverse from
`HasStrictDerivAt.localInverse`, and `Θ` is the eta-times-one
function (analytic by `etaTimesOne_chart_local_analytic`).
-/
theorem localPullbackAt_holomorphic_theorem
    [T2Space X] [T2Space Y] [Nonempty X]
    {f : X → Y} (h : BranchedCoverData X Y f)
    (hcompat : h.RamificationIndexCompatible)
    (hf : IsHolomorphic f)
    (ω : HolomorphicOneForm ℂ X)
    (x : X) (hx : h.ramificationIndex x = 1) :
    IsHolomorphicAt (localPullbackAt h hf ω x hx) (f x) := by
  classical
  -- Setup: chart-image basepoints + the chart-local map F of f at x.
  set z₀ : ℂ := chartAt ℂ x x with hz₀_def
  set w₀ : ℂ := chartAt ℂ (f x) (f x) with hw₀_def
  set F : ℂ → ℂ := chartLocalAt f x with hF_def
  have hfHolAt : IsHolomorphicAt f x := hf.holomorphicAt x
  have hF_an : AnalyticAt ℂ F z₀ := hfHolAt
  have hFz₀ : F z₀ = w₀ := by simp [F, z₀, w₀, chartLocalAt]
  -- ramification-index-1 ⇒ nonzero derivative at z₀ (chart-local).
  have hramAt : mapAnalyticOrderAt f x = 1 := by
    rw [← h.ramificationIndex_eq_mapAnalyticOrderAt hcompat hfHolAt]; exact hx
  have hderiv : deriv F z₀ ≠ 0 := by
    have h_order : analyticOrderAt
        (fun t => F t - F z₀) z₀ = 1 := by
      convert hramAt using 1
      unfold mapAnalyticOrderAt
      simp +decide [analyticOrderNatAt, F, z₀]
    have h_an : AnalyticAt ℂ (fun t => F t - F z₀) z₀ := hF_an.sub analyticAt_const
    have h_deriv_order : analyticOrderAt
        (deriv (fun t => F t - F z₀)) z₀ = 0 := by
      have := AnalyticAt.analyticOrderAt_deriv_add_one h_an
      aesop
    rw [analyticOrderAt_eq_zero] at h_deriv_order
    rcases h_deriv_order with hzero | hnezero
    · exfalso; exact hzero (AnalyticAt.deriv h_an)
    · simpa [deriv_sub_const] using hnezero
  -- Analytic local inverse r : ℂ → ℂ of F at z₀ (gives r(w₀) = z₀).
  have hSD : HasStrictDerivAt F (deriv F z₀) z₀ := hF_an.hasStrictDerivAt
  set r : ℂ → ℂ := hSD.localInverse F (deriv F z₀) z₀ hderiv with hr_def
  have hr_an_at_w₀ : AnalyticAt ℂ r w₀ := by
    rw [← hFz₀]
    simpa [r, hr_def] using hF_an.analyticAt_localInverse hderiv
  have hr_w₀ : r w₀ = z₀ := by
    have h_left : ∀ᶠ z in 𝓝 z₀, r (F z) = z := by
      simpa [r, hr_def] using hSD.eventually_left_inverse hderiv
    have := h_left.self_of_nhds
    rwa [hFz₀] at this
  have h_right_inv_F : ∀ᶠ z in 𝓝 w₀, F (r z) = z := by
    have h := hSD.eventually_right_inverse hderiv
    rw [hFz₀] at h
    simpa [r, hr_def] using h
  -- Continuity / tendsto for chart-symm compositions.
  have hr_tendsto : Tendsto r (𝓝 w₀) (𝓝 z₀) := by
    have := hr_an_at_w₀.continuousAt
    rwa [ContinuousAt, hr_w₀] at this
  have h_chartXsymm_z₀ : (chartAt ℂ x).symm z₀ = x := by
    simp [z₀, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
  have h_chartYsymm_w₀ : (chartAt ℂ (f x)).symm w₀ = f x := by
    simp [w₀, (chartAt ℂ (f x)).left_inv (mem_chart_source ℂ (f x))]
  have h_chartXsymm_tendsto : Tendsto (fun z : ℂ => (chartAt ℂ x).symm z)
      (𝓝 z₀) (𝓝 x) := by
    have hcont := (chartAt ℂ x).continuousAt_symm
      ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
    change Tendsto (fun z => (chartAt ℂ x).symm z) (𝓝 z₀)
      (𝓝 ((chartAt ℂ x).symm z₀)) at hcont
    rwa [h_chartXsymm_z₀] at hcont
  have h_chartYsymm_tendsto : Tendsto (fun z : ℂ => (chartAt ℂ (f x)).symm z)
      (𝓝 w₀) (𝓝 (f x)) := by
    have hcont := (chartAt ℂ (f x)).continuousAt_symm
      ((chartAt ℂ (f x)).map_source (mem_chart_source ℂ (f x)))
    change Tendsto (fun z => (chartAt ℂ (f x)).symm z) (𝓝 w₀)
      (𝓝 ((chartAt ℂ (f x)).symm w₀)) at hcont
    rwa [h_chartYsymm_w₀] at hcont
  have h_anal_inv_tendsto : Tendsto (fun z : ℂ => (chartAt ℂ x).symm (r z))
      (𝓝 w₀) (𝓝 x) := h_chartXsymm_tendsto.comp hr_tendsto
  -- BCD local-bijection extraction.
  obtain ⟨U, V, hUopen, hVopen, hxU, hfxV, hbij, hright_branch, hleft_branch⟩ :=
    h.localInverse_is_inverse hx
  -- Eventually-y' is in V; (chart X).symm (r z) is in U; and (chart X).symm (r z) is in chart source.
  have h_y'_in_V : ∀ᶠ z in 𝓝 w₀, (chartAt ℂ (f x)).symm z ∈ V :=
    h_chartYsymm_tendsto.eventually (hVopen.mem_nhds hfxV)
  have h_anal_inv_in_U : ∀ᶠ z in 𝓝 w₀, (chartAt ℂ x).symm (r z) ∈ U :=
    h_anal_inv_tendsto.eventually (hUopen.mem_nhds hxU)
  have h_anal_inv_in_chart_source : ∀ᶠ z in 𝓝 w₀,
      (chartAt ℂ x).symm (r z) ∈ (chartAt ℂ x).source :=
    h_anal_inv_tendsto.eventually
      ((chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x))
  -- Eventually localInverseAt y' = (chart X).symm (r z) (uniqueness of local inverse).
  have h_localInv_eq : ∀ᶠ z in 𝓝 w₀,
      h.localInverseAt x hx ((chartAt ℂ (f x)).symm z) =
        (chartAt ℂ x).symm (r z) := by
    -- Goal: f ((chart X).symm (r z)) = (chart Y).symm z eventually,
    --       and (chart X).symm (r z) ∈ U,
    -- then hleft_branch ((chart X).symm (r z)) hxU' gives the conclusion.
    have h_f_anal_inv_in_src : ∀ᶠ z in 𝓝 w₀,
        f ((chartAt ℂ x).symm (r z)) ∈ (chartAt ℂ (f x)).source := by
      have htendsto : Tendsto (fun z => f ((chartAt ℂ x).symm (r z))) (𝓝 w₀)
          (𝓝 (f x)) := (hf.continuous.continuousAt (x := x)).tendsto.comp h_anal_inv_tendsto
      exact htendsto.eventually
        ((chartAt ℂ (f x)).open_source.mem_nhds (mem_chart_source ℂ (f x)))
    have h_z_in_target : ∀ᶠ z in 𝓝 w₀, z ∈ (chartAt ℂ (f x)).target :=
      chart_target_mem_nhds ℂ (f x)
    have h_f_eq : ∀ᶠ z in 𝓝 w₀,
        f ((chartAt ℂ x).symm (r z)) = (chartAt ℂ (f x)).symm z := by
      filter_upwards [h_right_inv_F, h_anal_inv_in_chart_source, h_z_in_target,
        h_f_anal_inv_in_src]
        with z h_FrZ h_anal_in_src h_z_target h_f_anal_in_src
      have hF_unfold : F (r z) = chartAt ℂ (f x) (f ((chartAt ℂ x).symm (r z))) := by
        simp [F, chartLocalAt, Function.comp_apply]
      rw [hF_unfold] at h_FrZ
      have h_apply : (chartAt ℂ (f x)).symm
          (chartAt ℂ (f x) (f ((chartAt ℂ x).symm (r z)))) =
          (chartAt ℂ (f x)).symm z := by rw [h_FrZ]
      rw [(chartAt ℂ (f x)).left_inv h_f_anal_in_src] at h_apply
      exact h_apply
    filter_upwards [h_f_eq, h_anal_inv_in_U] with z h_f_eq h_anal_in_U
    have h_lb := hleft_branch ((chartAt ℂ x).symm (r z)) h_anal_in_U
    rw [h_f_eq] at h_lb
    exact h_lb
  -- Define Θ (analytic at z₀ by etaTimesOne_chart_local_analytic).
  set Θ : ℂ → ℂ := fun ε => (ω.toFun ((chartAt ℂ x).symm ε)) (1 : ℂ) with hΘ_def
  have hΘ_an : AnalyticAt ℂ Θ z₀ := by
    simpa [Θ, z₀] using etaTimesOne_chart_local_analytic ω x
  -- Candidate function: chartCand z := (deriv F (r z))⁻¹ * Θ(r z).
  -- Analytic at w₀ via composition + product + inverse-of-nonzero-analytic.
  have h_derivF_an : AnalyticAt ℂ (deriv F) z₀ := hF_an.deriv
  have h_derivF_circ_r_an : AnalyticAt ℂ (fun z => deriv F (r z)) w₀ := by
    have h_derivF_an' : AnalyticAt ℂ (deriv F) (r w₀) := by rw [hr_w₀]; exact h_derivF_an
    exact h_derivF_an'.comp hr_an_at_w₀
  have h_derivF_circ_r_ne : (fun z => deriv F (r z)) w₀ ≠ 0 := by
    show deriv F (r w₀) ≠ 0; rw [hr_w₀]; exact hderiv
  have h_inv_an : AnalyticAt ℂ (fun z => (deriv F (r z))⁻¹) w₀ :=
    h_derivF_circ_r_an.inv h_derivF_circ_r_ne
  have hΘ_circ_r_an : AnalyticAt ℂ (fun z => Θ (r z)) w₀ := by
    have hΘ_an' : AnalyticAt ℂ Θ (r w₀) := by rw [hr_w₀]; exact hΘ_an
    exact hΘ_an'.comp hr_an_at_w₀
  have h_chartCand_an : AnalyticAt ℂ
      (fun z => (deriv F (r z))⁻¹ * Θ (r z)) w₀ :=
    h_inv_an.mul hΘ_circ_r_an
  -- Now bridge to the goal. IsHolomorphicAt unfolds to AnalyticAt of chartLocalAt at chartAt point.
  -- chartLocalAt (localPullbackAt h hf ω x hx) (f x) z =
  --   chartAt ℂ (localPullbackAt h hf ω x hx (f x))
  --     (localPullbackAt h hf ω x hx ((chartAt ℂ (f x)).symm z))
  -- The codomain chart on CotangentModelFiber ℂ is singleton-based on cotangentFiberIso,
  -- so it acts as cotangentFiberIso on every input.
  -- We use congr_of_eventuallyEq with the analytic candidate.
  unfold IsHolomorphicAt chartLocalAt
  -- Goal: AnalyticAt ℂ (fun z => chartAt ℂ (localPullbackAt … (f x))
  --         (localPullbackAt … ((chartAt ℂ (f x)).symm z))) w₀
  refine h_chartCand_an.congr ?_
  -- Show eventually: the candidate equals the chart-local localPullbackAt.
  -- For y' near f x with all eventually-conditions:
  --   localPullbackAt y' = cotangentPushforward f x' (ω.toFun x') where x' = localInverseAt y'.
  --   By cotangentPushforward_apply_one (at unramified x'):
  --   (cotangentPushforward f x' (ω.toFun x')) 1
  --     = (deriv (chartLocalAt f x') (chartAt ℂ x' x'))⁻¹ • (ω.toFun x') 1.
  -- Under StableChartAt + the localInverse identification, this collapses to
  --   (deriv F (r z))⁻¹ * Θ(r z) = chartCand z.
  have h_evt_unram : ∀ᶠ z in 𝓝 w₀,
      h.ramificationIndex (h.localInverseAt x hx ((chartAt ℂ (f x)).symm z)) = 1 :=
    h_chartYsymm_tendsto.eventually
      (h.localInverseAt_eventually_unramified x hx)
  -- eventually z ∈ (chart Y).target.
  have h_z_in_target_evt : ∀ᶠ z in 𝓝 w₀, z ∈ (chartAt ℂ (f x)).target :=
    chart_target_mem_nhds ℂ (f x)
  -- eventually r z ∈ (chart X).target. (r is continuous at w₀ with r w₀ = z₀ ∈ chart target.)
  have h_rz_in_target_evt : ∀ᶠ z in 𝓝 w₀, r z ∈ (chartAt ℂ x).target := by
    have h_z₀_in_target : z₀ ∈ (chartAt ℂ x).target := by
      show chartAt ℂ x x ∈ (chartAt ℂ x).target
      exact (chartAt ℂ x).map_source (mem_chart_source ℂ x)
    exact hr_tendsto.eventually ((chartAt ℂ x).open_target.mem_nhds h_z₀_in_target)
  filter_upwards [h_localInv_eq, h_evt_unram, h_anal_inv_in_chart_source,
    h_y'_in_V, h_z_in_target_evt, h_rz_in_target_evt]
    with z h_loc_eq h_unram h_anal_in_src h_y_in_V h_z_in_target h_rz_in_target
  -- Set x' := localInverseAt ((chart Y).symm z) = (chart X).symm (r z).
  set y' : Y := (chartAt ℂ (f x)).symm z with hy'_def
  set x' : X := h.localInverseAt x hx y' with hx'_def
  have hx'_alt : x' = (chartAt ℂ x).symm (r z) := h_loc_eq
  -- StableChartAt: chartAt ℂ x' = chartAt ℂ x (since x' is in chart source of x).
  have h_chart_eq : chartAt ℂ x' = chartAt ℂ x :=
    JacobianChallenge.Periods.StableChartAt.chartAt_eq_of_mem_source
      x x' (by rw [hx'_alt]; exact h_anal_in_src)
  -- chartAt ℂ x' x' = chartAt ℂ x x' = r z (chart roundtrip on the chart-source side).
  have h_chartAt_x'_x' : chartAt ℂ x' x' = r z := by
    rw [h_chart_eq, hx'_alt]
    exact (chartAt ℂ x).right_inv h_rz_in_target
  -- f x' = y' = (chart Y).symm z (using BCD right-branch on V).
  have hfx'_eq_y' : f x' = (chartAt ℂ (f x)).symm z := by
    show f (h.localInverseAt x hx y') = (chartAt ℂ (f x)).symm z
    exact hright_branch y' h_y_in_V
  -- f x' ∈ (chart Y).source from z ∈ (chart Y).target.
  have h_fx'_in_chartY_source : f x' ∈ (chartAt ℂ (f x)).source := by
    rw [hfx'_eq_y']
    exact (chartAt ℂ (f x)).map_target h_z_in_target
  have h_chartY_eq : chartAt ℂ (f x') = chartAt ℂ (f x) :=
    JacobianChallenge.Periods.StableChartAt.chartAt_eq_of_mem_source
      (f x) (f x') h_fx'_in_chartY_source
  -- Under h_chart_eq and h_chartY_eq, chartLocalAt f x' = chartLocalAt f x = F.
  have h_chartLocalAt_eq : chartLocalAt f x' = F := by
    show chartAt ℂ (f x') ∘ f ∘ (chartAt ℂ x').symm = chartLocalAt f x
    rw [h_chartY_eq, h_chart_eq]
    rfl
  -- Now: cotangentPushforward_apply_one (de-privatized in this commit) gives the chart-local formula.
  have h_cp_apply :=
    cotangentPushforward_apply_one (f := f) h hcompat hf (x := x') h_unram (ω.toFun x')
  -- h_cp_apply :
  -- (cotangentPushforward f x' (ω.toFun x')) 1 =
  --   (deriv (chartLocalAt f x') (chart x' x'))⁻¹ • (ω.toFun x') 1
  -- Substitute h_chartLocalAt_eq and h_chartAt_x'_x':
  -- (cotangentPushforward f x' (ω.toFun x')) 1 = (deriv F (r z))⁻¹ • (ω.toFun x') 1.
  -- Also: (ω.toFun x') 1 = Θ (r z) since x' = (chart X).symm (r z).
  have h_eta_eq : (ω.toFun x') (1 : ℂ) = Θ (r z) := by
    show (ω.toFun x') (1 : ℂ) = (ω.toFun ((chartAt ℂ x).symm (r z))) (1 : ℂ)
    rw [hx'_alt]
  -- The chart on CotangentModelFiber ℂ is the singleton chart sending T to T 1.
  -- After unfold, goal becomes:
  --   (deriv F (r z))⁻¹ * Θ (r z) =
  --     (chartAt ℂ (localPullbackAt … (f x)) ∘ localPullbackAt … ∘ (chart Y).symm) z
  -- Simplify the composition and chain through cotangentFiberIso, cotangentPushforward_apply_one.
  symm
  show (chartAt ℂ (localPullbackAt h hf ω x hx (f x))
      (localPullbackAt h hf ω x hx ((chartAt ℂ (f x)).symm z)))
    = (deriv F (r z))⁻¹ * Θ (r z)
  -- Unfold localPullbackAt:
  show (chartAt ℂ (localPullbackAt h hf ω x hx (f x))
      (cotangentPushforward f x' (ω.toFun x')))
    = (deriv F (r z))⁻¹ * Θ (r z)
  -- The chart at any cotangent-fiber point is the singleton chart from cotangentFiberIso.
  -- For a CLM T : ℂ →L[ℂ] ℂ, this evaluates to cotangentFiberIso T = T 1.
  have h_chart_eq_iso : (chartAt ℂ (localPullbackAt h hf ω x hx (f x))
      (cotangentPushforward f x' (ω.toFun x')))
    = (cotangentPushforward f x' (ω.toFun x')) (1 : ℂ) := rfl
  rw [h_chart_eq_iso, h_cp_apply, h_chartLocalAt_eq, h_chartAt_x'_x', h_eta_eq]
  -- Goal: (deriv F (r z))⁻¹ • Θ (r z) = (deriv F (r z))⁻¹ * Θ (r z) — ℂ scalars.
  exact smul_eq_mul _ _

end JacobianChallenge.HolomorphicForms
