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

open scoped Manifold Topology BigOperators Classical
open Set Filter

/-! ### Tangent-space scalar instances

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

/-- A value `y : Y` is regular for the branched cover `f` if no preimage
of `y` is a ramification point. -/
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

/-- The pushforward of a cotangent vector along a local diffeomorphism.
Given `f : X → Y` and `x` such that `df_x` is an isomorphism, push
`ωx ∈ T_x^* X` to `T_{f x}^* Y`. -/
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

/-- Local re-statement of
`JacobianChallenge.Blueprint.mapAnalyticOrderAt_eq_one_iff_chartLocal_deriv_ne_zero`
(in `Jacobian/Blueprint/Sec02/WeightedFiberCardConst.lean`), inlined
here because that blueprint file is currently broken upstream. -/
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
    (_hf : IsHolomorphic f)
    (x : X) (hx : h.ramificationIndex x = 1) :
    IsHolomorphicAt (h.localInverseAt x hx) (f x) := by
  obtain ⟨U, _V, hU_open, _hV_open, hxU, _hfxV, _hfBij, _hf_right, hf_left⟩ :=
    h.localInverse_is_inverse hx
  have hfx_hol : IsHolomorphicAt f x := _hf.holomorphicAt x
  have hramAt : mapAnalyticOrderAt f x = 1 := by
    rw [← h.ramificationIndex_eq_mapAnalyticOrderAt hfx_hol]; exact hx
  have hderiv : deriv (chartLocalAt f x) (chartAt ℂ x x) ≠ 0 :=
    (_mapAnalyticOrderAt_eq_one_iff_chartLocal_deriv_ne_zero hfx_hol).mp hramAt
  set g : ℂ → ℂ := chartLocalAt f x with hg_def
  set c : ℂ := chartAt ℂ x x with hc_def
  have hgc : g c = chartAt ℂ (f x) (f x) := chartLocalAt_chartAt_self f x
  have hg_analytic : AnalyticAt ℂ g c := hfx_hol
  have hg_strict : HasStrictDerivAt g (deriv g c) c := hg_analytic.hasStrictDerivAt
  set r : ℂ → ℂ := hg_strict.localInverse g (deriv g c) c hderiv with hr_def
  have hr_analytic : AnalyticAt ℂ r (g c) := hg_analytic.analyticAt_localInverse hderiv
  have h_locinv_fx : h.localInverseAt x hx (f x) = x := hf_left x hxU
  -- Reduce the goal via congruence with `r`.
  show AnalyticAt ℂ (chartLocalAt (h.localInverseAt x hx) (f x)) (chartAt ℂ (f x) (f x))
  rw [← hgc]
  refine hr_analytic.congr ?_
  -- Establish the eventual equality
  -- `r t = chartLocalAt (h.localInverseAt x hx) (f x) t` for `t` near `g c`.
  have hf_cont : ContinuousAt f x := _hf.continuous.continuousAt
  have hr_left : ∀ᶠ z in 𝓝 c, r (g z) = z := hg_strict.eventually_left_inverse hderiv
  have hr_right : ∀ᶠ t in 𝓝 (g c), g (r t) = t := hg_strict.eventually_right_inverse hderiv
  have hr_at : r (g c) = c := hr_left.self_of_nhds
  have hr_cont : ContinuousAt r (g c) := hr_analytic.continuousAt
  have h_symm_cont_x : ContinuousAt (chartAt ℂ x).symm c :=
    (chartAt ℂ x).continuousAt_symm (mem_chart_target ℂ x)
  have h_symm_at_x : (chartAt ℂ x).symm c = x :=
    (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
  have e1 : ∀ᶠ t in 𝓝 (g c), r t ∈ (chartAt ℂ x).target :=
    hr_cont.preimage_mem_nhds (by
      rw [hr_at]
      exact (chartAt ℂ x).open_target.mem_nhds (mem_chart_target ℂ x))
  have h_symm_r_cont : ContinuousAt (fun t => (chartAt ℂ x).symm (r t)) (g c) :=
    h_symm_cont_x.comp_of_eq hr_cont hr_at
  have e2 : ∀ᶠ t in 𝓝 (g c), (chartAt ℂ x).symm (r t) ∈ U := by
    refine h_symm_r_cont.preimage_mem_nhds ?_
    show U ∈ 𝓝 ((chartAt ℂ x).symm (r (g c)))
    rw [hr_at, h_symm_at_x]
    exact hU_open.mem_nhds hxU
  have e3 : ∀ᶠ t in 𝓝 (g c), t ∈ (chartAt ℂ (f x)).target := by
    rw [hgc]
    exact (chartAt ℂ (f x)).open_target.mem_nhds (mem_chart_target ℂ (f x))
  have e5 : ∀ᶠ t in 𝓝 (g c), f ((chartAt ℂ x).symm (r t)) ∈ (chartAt ℂ (f x)).source := by
    have h_cont : ContinuousAt (fun t => f ((chartAt ℂ x).symm (r t))) (g c) :=
      hf_cont.comp_of_eq h_symm_r_cont (by rw [hr_at, h_symm_at_x])
    refine h_cont.preimage_mem_nhds ?_
    show (chartAt ℂ (f x)).source ∈ 𝓝 (f ((chartAt ℂ x).symm (r (g c))))
    rw [hr_at, h_symm_at_x]
    exact chart_source_mem_nhds ℂ (f x)
  filter_upwards [e1, e2, e3, e5, hr_right] with t ht1 ht2 ht3 ht5 ht6
  -- Goal: `r t = chartLocalAt (h.localInverseAt x hx) (f x) t`.
  have hy_source : (chartAt ℂ (f x)).symm t ∈ (chartAt ℂ (f x)).source :=
    (chartAt ℂ (f x)).map_target ht3
  have hy_eq : chartAt ℂ (f x) ((chartAt ℂ (f x)).symm t) = t :=
    (chartAt ℂ (f x)).right_inv ht3
  have hfut_eq : chartAt ℂ (f x) (f ((chartAt ℂ x).symm (r t))) = t := ht6
  have hfut_eq_yt :
      f ((chartAt ℂ x).symm (r t)) = (chartAt ℂ (f x)).symm t :=
    (chartAt ℂ (f x)).injOn ht5 hy_source (by rw [hfut_eq, hy_eq])
  have hlocinv_eq :
      h.localInverseAt x hx ((chartAt ℂ (f x)).symm t) = (chartAt ℂ x).symm (r t) := by
    rw [← hfut_eq_yt]
    exact hf_left _ ht2
  show r t = chartLocalAt (h.localInverseAt x hx) (f x) t
  show r t = chartAt ℂ (h.localInverseAt x hx (f x))
        (h.localInverseAt x hx ((chartAt ℂ (f x)).symm t))
  rw [hlocinv_eq, h_locinv_fx, (chartAt ℂ x).right_inv ht1]

/-- The pullback of a holomorphic form along a local inverse branch. -/
noncomputable def localPullbackAt
    {f : X → Y} (h : BranchedCoverData X Y f)
    (_hf : IsHolomorphic f)
    (ω : HolomorphicOneForm ℂ X)
    (x : X) (hx : h.ramificationIndex x = 1) :
    Y → CotangentModelFiber ℂ :=
  fun y' => cotangentPushforward f (h.localInverseAt x hx y') (ω.toFun (h.localInverseAt x hx y'))

/-- Pullback of a holomorphic form along a local inverse branch is holomorphic. -/
theorem localPullbackAt_holomorphic
    {f : X → Y} (h : BranchedCoverData X Y f)
    (hf : IsHolomorphic f)
    (ω : HolomorphicOneForm ℂ X)
    (x : X) (hx : h.ramificationIndex x = 1) :
    IsHolomorphicAt (localPullbackAt h hf ω x hx) (f x) := by
  sorry

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
    (hf : IsHolomorphic f)
    (ω : HolomorphicOneForm ℂ X)
    (y : Y) (hy : isRegularValue h y) :
    IsHolomorphicAt (localTraceAtRegularValue h hf ω y hy) y := by
  sorry

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

/-! ### Analytic bridge: ramification index 1 ⇒ mfderiv is an iso. -/

/-- **Analytic bridge.** At an unramified point of a branched cover,
the manifold derivative `mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x` is a continuous
linear isomorphism `TangentSpace 𝓘 x →L[ℂ] TangentSpace 𝓘 (f x)`,
given that `f` is holomorphic and continuous at `x`. -/
theorem mfderiv_isIso_of_ramificationIndex_one
    {f : X → Y} (h : BranchedCoverData X Y f) (hf : IsHolomorphic f) {x : X}
    (hx : h.ramificationIndex x = 1) :
    Nonempty (IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x)) := by
  have hramAt : mapAnalyticOrderAt f x = 1 := by
    rw [← h.ramificationIndex_eq_mapAnalyticOrderAt (hf.holomorphicAt x)]
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

/-- The trace of a pullback is scaled by the degree (at regular values).

The smoothness hypothesis `hf` provides the chain-rule pullback's
underlying function (via `pullbackFormsBundled`) and, through a private
`ContMDiff → IsHolomorphic` bridge, the analytic data used by
`mfderiv_isIso_of_ramificationIndex_one`. -/
theorem trace_pullback_at_regular_value
    {f : X → Y} (h : BranchedCoverData X Y f)
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
      mfderiv_isIso_of_ramificationIndex_one h hHol hx_unram
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
