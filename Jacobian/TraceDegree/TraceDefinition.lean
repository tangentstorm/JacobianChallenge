import Jacobian.HolomorphicForms.BranchedCover
import Jacobian.HolomorphicForms.CotangentBundle
import Jacobian.HolomorphicForms.PullbackBundled
import Jacobian.HolomorphicForms.HolomorphicMap
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Trace (pushforward) of differential forms along a branched cover

This file defines the trace (pushforward) of differential 1-forms along
a branched cover `f : X → Y`.
-/

namespace JacobianChallenge.HolomorphicForms

set_option linter.unusedSectionVars false

open scoped Manifold Topology BigOperators Classical
open Set Filter

/-!
### Tangent-space scalar instances

`TangentSpace 𝓘(ℂ, ℂ) z = ℂ` definitionally, but the `def` is *not*
reducible so type-class inference does not transport the
`NormedAddCommGroup` / `NormedSpace ℂ` instances on `ℂ` to
`TangentSpace 𝓘(ℂ, ℂ) z` automatically.  We supply them as scoped
instances so consumers inside `JacobianChallenge.HolomorphicForms`
can synthesise the `IsIso` predicate below on `mfderiv 𝓘(ℂ, ℂ) …`.
-/

noncomputable scoped instance tangentSpace_complex_normedAddCommGroup
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z] (z : Z) :
    NormedAddCommGroup (TangentSpace 𝓘(ℂ, ℂ) z) :=
  inferInstanceAs (NormedAddCommGroup ℂ)

noncomputable scoped instance tangentSpace_complex_normedSpace
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z] (z : Z) :
    NormedSpace ℂ (TangentSpace 𝓘(ℂ, ℂ) z) :=
  inferInstanceAs (NormedSpace ℂ ℂ)

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
variable [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
variable [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
variable [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]

/--
A value `y : Y` is regular for the branched cover `f` if no preimage
of `y` is a ramification point.
-/
def isRegularValue {f : X → Y} (h : BranchedCoverData X Y f) (y : Y) : Prop :=
  ∀ x ∈ f ⁻¹' {y}, h.ramificationIndex x = 1

/-- The regular locus of a branched cover. -/
def regularLocus {f : X → Y} (h : BranchedCoverData X Y f) : Set Y :=
  {y | isRegularValue h y}

/-- Predicate for a continuous linear map being an isomorphism. -/
structure IsIso {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (f : E →L[ℂ] F) where
  inv : F →L[ℂ] E
  left_inv : inv.comp f = ContinuousLinearMap.id ℂ E
  right_inv : f.comp inv = ContinuousLinearMap.id ℂ F

/--
The pushforward of a cotangent vector along a local diffeomorphism.
Given `f : X → Y` and `x` such that `df_x` is an isomorphism, push
`ωx ∈ T_x^* X` to `T_{f x}^* Y`.
-/
noncomputable def cotangentPushforward
    (f : X → Y) (x : X) (ωx : CotangentSpace ℂ X x) :
    CotangentSpace ℂ Y (f x) :=
  if h : Nonempty (IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x)) then
    ωx.comp (Classical.choice h).inv
  else
    0

/-- The trace of a 1-form at a regular value `y`. -/
noncomputable def traceAtRegularValue
    {f : X → Y} (h : BranchedCoverData X Y f)
    (ω : ∀ x, CotangentSpace ℂ X x)
    (y : Y) (_hy : isRegularValue h y) : CotangentSpace ℂ Y y :=
  let s := (h.finite_fiber y).toFinset
  Finset.sum s.attach (fun x => cotangentPushforward f x.1 (ω x.1))

/-! ### Analytic bridge: ramification index 1 ⇒ first-order local map. -/


private theorem _mapAnalyticOrderAt_eq_one_iff_chartLocal_deriv_ne_zero
    {f : X → Y} {x : X} (_hf : IsHolomorphicAt f x) :
    mapAnalyticOrderAt f x = 1 ↔ deriv (chartLocalAt f x) (chartAt ℂ x x) ≠ 0 := by
  constructor <;> intro h
  · have h_order : analyticOrderAt
        (fun t => chartLocalAt f x t - chartLocalAt f x (chartAt ℂ x x))
        (chartAt ℂ x x) = 1 := by
      convert h using 1
      unfold mapAnalyticOrderAt
      simp +decide [analyticOrderNatAt]
    have h_deriv : analyticOrderAt
        (deriv (fun t => chartLocalAt f x t - chartLocalAt f x (chartAt ℂ x x)))
        (chartAt ℂ x x) = 0 := by
      have := AnalyticAt.analyticOrderAt_deriv_add_one
        (show AnalyticAt ℂ
            (fun t => chartLocalAt f x t - chartLocalAt f x (chartAt ℂ x x))
            (chartAt ℂ x x) from ?_)
      · aesop
      · exact _hf.sub analyticAt_const
    rw [analyticOrderAt_eq_zero] at h_deriv
    simp_all +decide [deriv_sub_const]
    exact h_deriv.resolve_left fun h => h <| AnalyticAt.deriv _hf
  · unfold mapAnalyticOrderAt
    rw [analyticOrderNatAt]
    rw [AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero] <;> aesop

/-- The local inverse is holomorphic at `f x`. -/
theorem localInverseAt_holomorphic
    {f : X → Y} (h : BranchedCoverData X Y f)
    (hcompat : h.RamificationIndexCompatible)
    (_hf : IsHolomorphic f)
    (x : X) (hx : h.ramificationIndex x = 1) :
    IsHolomorphicAt (h.localInverseAt x hx) (f x) := by
  classical
  have hramAt : mapAnalyticOrderAt f x = 1 := by
    rw [← h.ramificationIndex_eq_mapAnalyticOrderAt hcompat (_hf.holomorphicAt x)]
    exact hx
  have hderiv : deriv (chartLocalAt f x) (chartAt ℂ x x) ≠ 0 :=
    (_mapAnalyticOrderAt_eq_one_iff_chartLocal_deriv_ne_zero
      (_hf.holomorphicAt x)).mp hramAt
  let analyticInv : Y → X := (_hf.holomorphicAt x).localInverse hderiv
  have hanalytic : IsHolomorphicAt analyticInv (f x) := by
    dsimp [analyticInv]
    exact (_hf.holomorphicAt x).localInverse_isHolomorphicAt hderiv
  refine hanalytic.congr_of_eventuallyEq ?_
  obtain ⟨U, _V, hUopen, _hVopen, hxU, _hfxV, _hbij, _hright_branch, hleft_branch⟩ :=
    h.localInverse_is_inverse hx
  let F : ℂ → ℂ := chartLocalAt f x
  let z₀ : ℂ := chartAt ℂ x x
  let w₀ : ℂ := chartAt ℂ (f x) (f x)
  let r : ℂ → ℂ :=
    (_hf.holomorphicAt x).hasStrictDerivAt.localInverse F
      (deriv F z₀) z₀ hderiv
  have hFz₀ : F z₀ = w₀ := by
    simp [F, z₀, w₀]
  have hr_z₀ : r w₀ = z₀ := by
    dsimp [r]
    rw [← hFz₀]
    exact (HasStrictDerivAt.eventually_left_inverse
      (f := F) (f' := deriv F z₀) (a := z₀)
      (hf := (_hf.holomorphicAt x).hasStrictDerivAt) (hf' := hderiv)).self_of_nhds
  have hlocalInv_tendsto : Tendsto analyticInv (𝓝 (f x)) (𝓝 x) := by
    have hr_an : AnalyticAt ℂ r w₀ := by
      dsimp [r, F, z₀, w₀]
      simpa [F, z₀, w₀, hFz₀] using
        (_hf.holomorphicAt x).analyticAt_localInverse hderiv
    have hr_tendsto : Tendsto r (𝓝 w₀) (𝓝 z₀) := by
      simpa [ContinuousAt, hr_z₀] using hr_an.continuousAt
    have hchart_tendsto : Tendsto (fun y : Y => chartAt ℂ (f x) y)
        (𝓝 (f x)) (𝓝 w₀) := by
      simpa [w₀] using (chartAt ℂ (f x)).continuousAt (mem_chart_source ℂ (f x))
    have hsymm_tendsto : Tendsto (fun z => (chartAt ℂ x).symm z)
        (𝓝 z₀) (𝓝 x) := by
      have hcont := (chartAt ℂ x).continuousAt_symm
        ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
      change Tendsto (fun z => (chartAt ℂ x).symm z) (𝓝 z₀)
        (𝓝 ((chartAt ℂ x).symm z₀)) at hcont
      simpa [z₀, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)] using hcont
    have hcomp := hsymm_tendsto.comp (hr_tendsto.comp hchart_tendsto)
    simpa [analyticInv, IsHolomorphicAt.localInverse, r, F, z₀, w₀] using hcomp
  have hanalyticInv_mem_U : ∀ᶠ y in 𝓝 (f x), analyticInv y ∈ U :=
    hlocalInv_tendsto.eventually (hUopen.mem_nhds hxU)
  have hanalyticInv_right : ∀ᶠ y in 𝓝 (f x), f (analyticInv y) = y := by
    have hright_z : ∀ᶠ z in 𝓝 w₀, F (r z) = z := by
      dsimp [r]
      simpa [F, z₀, w₀, hFz₀] using
        (HasStrictDerivAt.eventually_right_inverse
          (f := F) (f' := deriv F z₀) (a := z₀)
          (hf := (_hf.holomorphicAt x).hasStrictDerivAt) (hf' := hderiv))
    have hchart_tendsto : Tendsto (fun y : Y => chartAt ℂ (f x) y)
        (𝓝 (f x)) (𝓝 w₀) := by
      simpa [w₀] using (chartAt ℂ (f x)).continuousAt (mem_chart_source ℂ (f x))
    have hright_y : ∀ᶠ y in 𝓝 (f x), F (r (chartAt ℂ (f x) y)) =
        chartAt ℂ (f x) y :=
      hchart_tendsto.eventually hright_z
    have hy_source : ∀ᶠ y in 𝓝 (f x), y ∈ (chartAt ℂ (f x)).source :=
      (chartAt ℂ (f x)).open_source.mem_nhds (mem_chart_source ℂ (f x))
    have hf_analyticInv_source : ∀ᶠ y in 𝓝 (f x),
        f (analyticInv y) ∈ (chartAt ℂ (f x)).source := by
      have htendsto : Tendsto (fun y => f (analyticInv y)) (𝓝 (f x)) (𝓝 (f x)) :=
        Tendsto.comp _hf.continuous.continuousAt hlocalInv_tendsto
      exact htendsto.eventually
        ((chartAt ℂ (f x)).open_source.mem_nhds (mem_chart_source ℂ (f x)))
    filter_upwards [hright_y, hy_source, hf_analyticInv_source] with y hy_eq hy_src hfy_src
    have hchart : chartAt ℂ (f x) (f (analyticInv y)) = chartAt ℂ (f x) y := by
      simpa [analyticInv, IsHolomorphicAt.localInverse, F, r, z₀, w₀] using hy_eq
    exact (chartAt ℂ (f x)).injOn hfy_src hy_src hchart
  filter_upwards [hanalyticInv_mem_U, hanalyticInv_right] with y hy_an_U hy_an_right
  have hleft := hleft_branch (analyticInv y) hy_an_U
  rw [hy_an_right] at hleft
  exact hleft.symm

/-- The pullback of a holomorphic form along a local inverse branch. -/
noncomputable def localPullbackAt
    {f : X → Y} (h : BranchedCoverData X Y f)
    (_hf : IsHolomorphic f)
    (ω : HolomorphicOneForm ℂ X)
    (x : X) (hx : h.ramificationIndex x = 1) :
    Y → CotangentModelFiber ℂ :=
  fun y' => cotangentPushforward f (h.localInverseAt x hx y') (ω.toFun (h.localInverseAt x hx y'))

/--
Pullback of a holomorphic form along a local inverse branch is holomorphic.

This is the remaining local analytic section-regularity obligation for the
trace construction: combine holomorphicity of the inverse branch with smooth
holomorphic variation of the cotangent pushforward in local coordinates.
-/
axiom localPullbackAt_holomorphic
    {f : X → Y} (h : BranchedCoverData X Y f)
    (hcompat : h.RamificationIndexCompatible)
    (hf : IsHolomorphic f)
    (ω : HolomorphicOneForm ℂ X)
    (x : X) (hx : h.ramificationIndex x = 1) :
    IsHolomorphicAt (localPullbackAt h hf ω x hx) (f x)

omit [IsManifold 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) Y] in
/-- Holomorphic finite sums with values in the cotangent model fiber. -/
private theorem IsHolomorphicAt.sum_cotangentModelFiber
    {ι : Type*} {s : Finset ι} {f : ι → Y → CotangentModelFiber ℂ} {p : Y}
    (hf : ∀ i ∈ s, IsHolomorphicAt (f i) p) :
    IsHolomorphicAt (fun y => Finset.sum s (fun i => f i y)) p := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _hf
    change IsHolomorphicAt (fun _ : Y => (0 : CotangentModelFiber ℂ)) p
    unfold IsHolomorphicAt chartLocalAt
    simpa using (analyticAt_const :
      AnalyticAt ℂ
        (fun _ : ℂ => chartAt ℂ (0 : CotangentModelFiber ℂ) (0 : CotangentModelFiber ℂ))
        (chartAt ℂ p p))
  · intro a s ha ih hfs
    have ha_holo : IsHolomorphicAt (f a) p :=
      hfs a (Finset.mem_insert_self a s)
    have hs_holo : IsHolomorphicAt (fun y => Finset.sum s (fun i => f i y)) p :=
      ih fun i hi => hfs i (Finset.mem_insert_of_mem hi)
    unfold IsHolomorphicAt chartLocalAt at *
    simpa [Finset.sum_insert, ha, Pi.add_apply, Function.comp_def] using
      ha_holo.add hs_holo

/-- A local version of the trace sum, defined in a neighborhood of `y`. -/
noncomputable def localTraceAtRegularValue
    {f : X → Y} (h : BranchedCoverData X Y f)
    (hf : IsHolomorphic f)
    (ω : HolomorphicOneForm ℂ X)
    (y : Y) (hy : isRegularValue h y) :
    Y → CotangentModelFiber ℂ :=
  fun y' =>
    let s := (h.finite_fiber y).toFinset
    Finset.sum s.attach (fun x =>
      let hx_fiber : x.1 ∈ f ⁻¹' {y} := by
        have hx_mem := x.2
        rw [Set.Finite.mem_toFinset] at hx_mem
        exact hx_mem
      localPullbackAt h hf ω x.1 (hy x.1 hx_fiber) y'
    )

/-- The local trace is holomorphic at regular values. -/
theorem localTraceAtRegularValue_holomorphic
    {f : X → Y} (h : BranchedCoverData X Y f)
    (hcompat : h.RamificationIndexCompatible)
    (hf : IsHolomorphic f)
    (ω : HolomorphicOneForm ℂ X)
    (y : Y) (hy : isRegularValue h y) :
    IsHolomorphicAt (localTraceAtRegularValue h hf ω y hy) y := by
  unfold localTraceAtRegularValue
  refine IsHolomorphicAt.sum_cotangentModelFiber ?_
  rintro ⟨x, hx_mem⟩ _mem_attach
  have hx_fiber : x ∈ f ⁻¹' {y} := (Set.Finite.mem_toFinset _).mp hx_mem
  have hfx : f x = y := hx_fiber
  simpa [hfx] using
    (localPullbackAt_holomorphic h hcompat hf ω x (hy x hx_fiber))

/-- The trace sum is additive. -/
theorem traceAtRegularValue_add
    {f : X → Y} (h : BranchedCoverData X Y f)
    (ω₁ ω₂ : ∀ x, CotangentSpace ℂ X x)
    (y : Y) (hy : isRegularValue h y) :
    traceAtRegularValue h (fun x => ω₁ x + ω₂ x) y hy =
      traceAtRegularValue h ω₁ y hy + traceAtRegularValue h ω₂ y hy := by
  unfold traceAtRegularValue
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  rintro ⟨x, _⟩ _
  show cotangentPushforward f x (ω₁ x + ω₂ x) =
    cotangentPushforward f x (ω₁ x) + cotangentPushforward f x (ω₂ x)
  unfold cotangentPushforward
  by_cases hiso : Nonempty (IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x))
  · simp only [dif_pos hiso]
    exact ContinuousLinearMap.add_comp _ _ _
  · simp only [dif_neg hiso, add_zero]

/-- The trace sum preserves scalar multiplication. -/
theorem traceAtRegularValue_smul
    {f : X → Y} (h : BranchedCoverData X Y f)
    (c : ℂ) (ω : ∀ x, CotangentSpace ℂ X x)
    (y : Y) (hy : isRegularValue h y) :
    traceAtRegularValue h (fun x => c • ω x) y hy =
      c • traceAtRegularValue h ω y hy := by
  unfold traceAtRegularValue
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  rintro ⟨x, _⟩ _
  show cotangentPushforward f x (c • ω x) = c • cotangentPushforward f x (ω x)
  unfold cotangentPushforward
  by_cases hiso : Nonempty (IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x))
  · simp only [dif_pos hiso]
    exact ContinuousLinearMap.smul_comp c _ _
  · simp only [dif_neg hiso]
    exact (smul_zero (A := CotangentSpace ℂ Y (f x)) c).symm

/--
**Analytic bridge.** At an unramified point of a branched cover,
the manifold derivative `mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x` is a continuous
linear isomorphism `TangentSpace 𝓘 x →L[ℂ] TangentSpace 𝓘 (f x)`,
given that `f` is holomorphic and continuous at `x`.
-/
theorem mfderiv_isIso_of_ramificationIndex_one
    {f : X → Y} (h : BranchedCoverData X Y f)
    (hcompat : h.RamificationIndexCompatible) (hf : IsHolomorphic f) {x : X}
    (hx : h.ramificationIndex x = 1) :
    Nonempty (IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x)) := by
  have hramAt : mapAnalyticOrderAt f x = 1 := by
    rw [← h.ramificationIndex_eq_mapAnalyticOrderAt hcompat (hf.holomorphicAt x)]
    exact hx
  have hderiv : deriv (chartLocalAt f x) (chartAt ℂ x x) ≠ 0 :=
    (_mapAnalyticOrderAt_eq_one_iff_chartLocal_deriv_ne_zero
      (hf.holomorphicAt x)).mp hramAt
  set a : ℂ := deriv (chartLocalAt f x) (chartAt ℂ x x) with ha_def
  have hFD : HasFDerivAt (chartLocalAt f x)
      (ContinuousLinearMap.toSpanSingleton ℂ a) (chartAt ℂ x x) :=
    (hf.holomorphicAt x).hasStrictDerivAt.hasStrictFDerivAt.hasFDerivAt
  have hMF : HasMFDerivAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x
      (ContinuousLinearMap.toSpanSingleton ℂ a) := by
    refine ⟨hf.continuous.continuousAt, ?_⟩
    have hFD' : HasFDerivWithinAt (chartLocalAt f x)
        (ContinuousLinearMap.toSpanSingleton ℂ a) Set.univ (chartAt ℂ x x) :=
      hFD.hasFDerivWithinAt
    simpa [writtenInExtChartAt, chartLocalAt, Function.comp_def] using hFD'
  have hmFD : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x =
      ContinuousLinearMap.toSpanSingleton ℂ a := hMF.mfderiv
  refine ⟨{
    inv := (ContinuousLinearMap.toSpanSingleton ℂ (a⁻¹ : ℂ) :
      TangentSpace 𝓘(ℂ, ℂ) (f x) →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) x),
    left_inv := ?_,
    right_inv := ?_ }⟩
  · rw [hmFD]
    show ((ContinuousLinearMap.toSpanSingleton ℂ (a⁻¹ : ℂ)).comp
            (ContinuousLinearMap.toSpanSingleton ℂ a) :
            ℂ →L[ℂ] ℂ) = ContinuousLinearMap.id ℂ ℂ
    refine ContinuousLinearMap.ext fun r => ?_
    simp only [ContinuousLinearMap.comp_apply,
               ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
               ContinuousLinearMap.id_apply]
    rw [mul_assoc, mul_inv_cancel₀ hderiv, mul_one]
  · rw [hmFD]
    show ((ContinuousLinearMap.toSpanSingleton ℂ a).comp
            (ContinuousLinearMap.toSpanSingleton ℂ (a⁻¹ : ℂ)) :
            ℂ →L[ℂ] ℂ) = ContinuousLinearMap.id ℂ ℂ
    refine ContinuousLinearMap.ext fun r => ?_
    simp only [ContinuousLinearMap.comp_apply,
               ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
               ContinuousLinearMap.id_apply]
    rw [mul_assoc, inv_mul_cancel₀ hderiv, mul_one]

/--
The trace of a pullback is scaled by the degree (at regular values).

The smoothness hypothesis `hf` provides the chain-rule pullback's
underlying function (via `pullbackFormsBundled`) and, through a private
`ContMDiff → IsHolomorphic` bridge, the analytic data used by
`mfderiv_isIso_of_ramificationIndex_one`.
-/
theorem trace_pullback_at_regular_value
    {f : X → Y} (h : BranchedCoverData X Y f)
    (hcompat : h.RamificationIndexCompatible)
    (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (⊤ : WithTop ℕ∞) f)
    (hHol : IsHolomorphic f)
    (η : HolomorphicOneForm ℂ Y)
    (y : Y) (hy : isRegularValue h y) :
    traceAtRegularValue h (fun x => (pullbackFormsBundled f hf η).toFun x) y hy =
      (h.weightedFiberCard y : ℂ) • η.toFun y := by
  have hterm : ∀ z : { x // x ∈ (h.finite_fiber y).toFinset },
      cotangentPushforward f z.1
        ((pullbackFormsBundled f hf η).toFun z.1) = η.toFun y := by
    rintro ⟨x, hx_mem⟩
    have hx_fiber : x ∈ f ⁻¹' {y} := (Set.Finite.mem_toFinset _).mp hx_mem
    have hfx : f x = y := hx_fiber
    have hx_unram : h.ramificationIndex x = 1 := hy x hx_fiber
    have hiso : Nonempty (IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x)) :=
      mfderiv_isIso_of_ramificationIndex_one h hcompat hHol hx_unram
    show cotangentPushforward f x (pullbackFormsFunFiber f η x) = η.toFun y
    unfold cotangentPushforward pullbackFormsFunFiber
    simp only [dif_pos hiso]
    rw [ContinuousLinearMap.comp_assoc, (Classical.choice hiso).right_inv,
        ContinuousLinearMap.comp_id, hfx]
  unfold traceAtRegularValue
  rw [show ((h.finite_fiber y).toFinset).attach.sum
        (fun z : { x // x ∈ (h.finite_fiber y).toFinset } =>
          cotangentPushforward f z.1
            ((pullbackFormsBundled f hf η).toFun z.1)) =
      ((h.finite_fiber y).toFinset).attach.sum
        (fun _ : { x // x ∈ (h.finite_fiber y).toFinset } => η.toFun y)
      from Finset.sum_congr rfl (fun z _ => hterm z)]
  rw [Finset.sum_const, Finset.card_attach]
  have hcard : (h.finite_fiber y).toFinset.card = h.weightedFiberCard y := by
    show (h.finite_fiber y).toFinset.card =
      ((h.finite_fiber y).toFinset).sum h.ramificationIndex
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [Set.Finite.mem_toFinset] at hx
    exact (hy x hx).symm
  rw [hcard]
  exact (Nat.cast_smul_eq_nsmul (R := ℂ) (h.weightedFiberCard y) (η.toFun y)).symm

end JacobianChallenge.HolomorphicForms
