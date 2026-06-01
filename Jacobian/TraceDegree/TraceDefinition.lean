import Jacobian.HolomorphicForms.BranchedCover
import Jacobian.HolomorphicForms.CotangentBundle
import Jacobian.HolomorphicForms.PullbackBundled
import Jacobian.HolomorphicForms.HolomorphicMap
import Jacobian.HolomorphicForms.EvalAtOneHelper
import Jacobian.HolomorphicForms.TangentSpaceComplexBridge
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# Trace (pushforward) of differential forms along a branched cover

This file defines the trace (pushforward) of differential 1-forms along
a branched cover `f : X → Y`.
-/

namespace JacobianChallenge.HolomorphicForms

set_option linter.unusedSectionVars false
-- v4.31: `TangentSpace 𝓘(ℂ,ℂ) x` is a non-reducible synonym for `ℂ`, so `rw`/`simp`
-- with CLM lemmas (e.g. an `IsIso.right_inv` on `mfderiv`) can't match the fiber-typed
-- composition unless instance defeq is allowed to see through it.  Mirrors Mathlib's
-- own `Geometry.Manifold.Riemannian.Basic`.
set_option backward.isDefEq.respectTransparency false

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
      have hca : ContinuousAt (fun y : Y => chartAt ℂ (f x) y) (f x) :=
        (chartAt ℂ (f x)).continuousAt (mem_chart_source ℂ (f x))
      rw [show w₀ = chartAt ℂ (f x) (f x) from rfl]
      exact hca
    have hsymm_tendsto : Tendsto (fun z => (chartAt ℂ x).symm z)
        (𝓝 z₀) (𝓝 x) := by
      have hcont := (chartAt ℂ x).continuousAt_symm
        ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
      change Tendsto (fun z => (chartAt ℂ x).symm z) (𝓝 z₀)
        (𝓝 ((chartAt ℂ x).symm z₀)) at hcont
      simpa [z₀, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)] using hcont
    have hcomp := hsymm_tendsto.comp (hr_tendsto.comp hchart_tendsto)
    refine hcomp.congr fun y' => ?_
    simp only [analyticInv, IsHolomorphicAt.localInverse, r, F, z₀, Function.comp_apply]
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
      have hca : ContinuousAt (fun y : Y => chartAt ℂ (f x) y) (f x) :=
        (chartAt ℂ (f x)).continuousAt (mem_chart_source ℂ (f x))
      rw [show w₀ = chartAt ℂ (f x) (f x) from rfl]
      exact hca
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
      show chartLocalAt f x (r (chartAt ℂ (f x) y)) = chartAt ℂ (f x) y
      exact hy_eq
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

/-! ### Custom-axiom discharge — relocated from TraceSpec + LocalPullbackHolomorphic (M4-final).

The proof of `localPullbackAt_holomorphic` (formerly an axiom at the next
declaration) is assembled here from helpers that were previously scattered
across TraceSpec.lean (private) and LocalPullbackHolomorphic.lean (where the
M4b-final theorem lived). Moving them upstream of the axiom site resolves
the import-cycle that blocked an in-place delegation. -/

/--
**Inverse uniqueness for `IsIso`.** Two `IsIso` witnesses for the same
continuous linear map have equal `inv` fields. -/
theorem IsIso.inv_unique_local
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {φ : E →L[ℂ] F} (h₁ h₂ : IsIso φ) : h₁.inv = h₂.inv := by
  calc h₁.inv
      = h₁.inv.comp (ContinuousLinearMap.id ℂ F) := by ext x; simp
    _ = h₁.inv.comp (φ.comp h₂.inv) := by rw [h₂.right_inv]
    _ = (h₁.inv.comp φ).comp h₂.inv := by
        ext x; simp [ContinuousLinearMap.comp_apply]
    _ = (ContinuousLinearMap.id ℂ E).comp h₂.inv := by rw [h₁.left_inv]
    _ = h₂.inv := by ext x; simp

/--
**The `mfderiv` is iso at an unramified point of a branched cover.** -/
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

/-- **Explicit form of the `mfderiv` inverse at any holomorphic point.** -/
theorem mfderiv_isIso_inv_eq_toSpanSingleton_inv
    {f : X → Y} (hHol : IsHolomorphic f) (x : X)
    (hiso : IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x)) :
    hiso.inv =
      (ContinuousLinearMap.toSpanSingleton ℂ
        ((deriv (chartLocalAt f x) (chartAt ℂ x x))⁻¹) :
        TangentSpace 𝓘(ℂ, ℂ) (f x) →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) x) := by
  set a : ℂ := deriv (chartLocalAt f x) (chartAt ℂ x x) with ha_def
  have hFD : HasFDerivAt (chartLocalAt f x)
      (ContinuousLinearMap.toSpanSingleton ℂ a) (chartAt ℂ x x) :=
    (hHol.holomorphicAt x).hasStrictDerivAt.hasStrictFDerivAt.hasFDerivAt
  have hMF : HasMFDerivAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x
      (ContinuousLinearMap.toSpanSingleton ℂ a) := by
    refine ⟨hHol.continuous.continuousAt, ?_⟩
    have hFD' : HasFDerivWithinAt (chartLocalAt f x)
        (ContinuousLinearMap.toSpanSingleton ℂ a) Set.univ (chartAt ℂ x x) :=
      hFD.hasFDerivWithinAt
    simpa [writtenInExtChartAt, chartLocalAt, Function.comp_def] using hFD'
  have hmFD : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x =
      ContinuousLinearMap.toSpanSingleton ℂ a := hMF.mfderiv
  have hderiv : a ≠ 0 := by
    intro ha0
    have hright := hiso.right_inv
    have happ := congr_arg (fun (m : TangentSpace 𝓘(ℂ, ℂ) (f x) →L[ℂ]
      TangentSpace 𝓘(ℂ, ℂ) (f x)) => m (1 : TangentSpace 𝓘(ℂ, ℂ) (f x))) hright
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.id_apply] at happ
    set w : ℂ := (hiso.inv (1 : TangentSpace 𝓘(ℂ, ℂ) (f x)) : ℂ) with hw_def
    rw [hmFD] at happ
    have happ' : w • a = (1 : ℂ) := happ
    rw [ha0, smul_zero] at happ'
    exact one_ne_zero happ'.symm
  let isoExplicit : IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x) :=
  { inv := (ContinuousLinearMap.toSpanSingleton ℂ (a⁻¹ : ℂ) :
      TangentSpace 𝓘(ℂ, ℂ) (f x) →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) x),
    left_inv := by
      rw [hmFD]
      show ((ContinuousLinearMap.toSpanSingleton ℂ (a⁻¹ : ℂ)).comp
              (ContinuousLinearMap.toSpanSingleton ℂ a) :
              ℂ →L[ℂ] ℂ) = ContinuousLinearMap.id ℂ ℂ
      refine ContinuousLinearMap.ext fun r => ?_
      simp only [ContinuousLinearMap.comp_apply,
                 ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
                 ContinuousLinearMap.id_apply]
      rw [mul_assoc, mul_inv_cancel₀ hderiv, mul_one]
    right_inv := by
      rw [hmFD]
      show ((ContinuousLinearMap.toSpanSingleton ℂ a).comp
              (ContinuousLinearMap.toSpanSingleton ℂ (a⁻¹ : ℂ)) :
              ℂ →L[ℂ] ℂ) = ContinuousLinearMap.id ℂ ℂ
      refine ContinuousLinearMap.ext fun r => ?_
      simp only [ContinuousLinearMap.comp_apply,
                 ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
                 ContinuousLinearMap.id_apply]
      rw [mul_assoc, inv_mul_cancel₀ hderiv, mul_one] }
  exact IsIso.inv_unique_local hiso isoExplicit

/-- **Explicit chart-local form of `cotangentPushforward` at an unramified preimage.** -/
theorem cotangentPushforward_eq_comp_toSpanSingleton_inv
    {f : X → Y} (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible)
    (hHol : IsHolomorphic f)
    {x : X} (hx_unram : hbc.ramificationIndex x = 1)
    (ωx : CotangentSpace ℂ X x) :
    cotangentPushforward f x ωx =
      ωx.comp
        (ContinuousLinearMap.toSpanSingleton ℂ
          ((deriv (chartLocalAt f x) (chartAt ℂ x x))⁻¹) :
          TangentSpace 𝓘(ℂ, ℂ) (f x) →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) x) := by
  classical
  have hiso : Nonempty (IsIso (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x)) :=
    mfderiv_isIso_of_ramificationIndex_one hbc hcompat hHol hx_unram
  unfold cotangentPushforward
  simp only [dif_pos hiso]
  rw [mfderiv_isIso_inv_eq_toSpanSingleton_inv hHol x (Classical.choice hiso)]

/-- **Single-summand explicit ℂ-scalar form: evaluating `cotangentPushforward` at 1.** -/
theorem cotangentPushforward_apply_one
    {f : X → Y} (hbc : BranchedCoverData X Y f)
    (hcompat : hbc.RamificationIndexCompatible)
    (hHol : IsHolomorphic f)
    {x : X} (hx_unram : hbc.ramificationIndex x = 1)
    (ωx : CotangentSpace ℂ X x) :
    (cotangentPushforward f x ωx) (1 : TangentSpace 𝓘(ℂ, ℂ) (f x)) =
      ((deriv (chartLocalAt f x) (chartAt ℂ x x))⁻¹) •
        ωx (1 : TangentSpace 𝓘(ℂ, ℂ) x) := by
  rw [cotangentPushforward_eq_comp_toSpanSingleton_inv hbc hcompat hHol hx_unram ωx]
  show ωx ((ContinuousLinearMap.toSpanSingleton ℂ
      ((deriv (chartLocalAt f x) (chartAt ℂ x x))⁻¹))
      (1 : TangentSpace 𝓘(ℂ, ℂ) (f x))) =
    ((deriv (chartLocalAt f x) (chartAt ℂ x x))⁻¹) •
      ωx (1 : TangentSpace 𝓘(ℂ, ℂ) x)
  rw [ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  conv_lhs => rw [show ((deriv (chartLocalAt f x) (chartAt ℂ x x))⁻¹ :
      TangentSpace 𝓘(ℂ, ℂ) x) =
      ((deriv (chartLocalAt f x) (chartAt ℂ x x))⁻¹ : ℂ) •
        (1 : TangentSpace 𝓘(ℂ, ℂ) x) from by
    show ((deriv (chartLocalAt f x) (chartAt ℂ x x))⁻¹ : ℂ) =
        ((deriv (chartLocalAt f x) (chartAt ℂ x x))⁻¹ : ℂ) * (1 : ℂ)
    rw [mul_one]]
  rw [ContinuousLinearMap.map_smul]

/--
**Eventually-unramified at the local inverse (M4-prep).**

For an unramified preimage `x` of `f x`, the local inverse maps a
neighborhood of `f x` into the unramified locus of `f`.
-/
theorem BranchedCoverData.localInverseAt_eventually_unramified
    [T2Space X] [T2Space Y]
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

/--
**Chart-local analyticity of `ω.toFun · 1`.**
For a holomorphic 1-form `ω` on `X` and base point `x₀`, the function
`ε ↦ (ω.toFun ((chartAt ℂ x₀).symm ε)) 1` is analytic at `chartAt ℂ x₀ x₀`.
-/
theorem etaTimesOne_chart_local_analytic
    [JacobianChallenge.Periods.StableChartAt ℂ X]
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

/--
Pullback of a holomorphic form along a local inverse branch is holomorphic.

This is the **discharge** of the former axiom `localPullbackAt_holomorphic`
(formerly at this site as an `axiom`). The proof passes through the singleton
chart on `CotangentModelFiber ℂ` (`cotangentFiberIso`), reducing to analyticity
of a ℂ-valued chart-local function. Under `StableChartAt`, the chart-local
form collapses to `z ↦ (deriv F (r z))⁻¹ * Θ(r z)` where `F := chartLocalAt f x`,
`r : ℂ → ℂ` is the analytic local inverse from `HasStrictDerivAt.localInverse`,
and `Θ` is the eta-times-one function (analytic by `etaTimesOne_chart_local_analytic`).
-/
theorem localPullbackAt_holomorphic
    [T2Space X] [T2Space Y]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [JacobianChallenge.Periods.StableChartAt ℂ Y]
    {f : X → Y} (h : BranchedCoverData X Y f)
    (hcompat : h.RamificationIndexCompatible)
    (hf : IsHolomorphic f)
    (ω : HolomorphicOneForm ℂ X)
    (x : X) (hx : h.ramificationIndex x = 1) :
    IsHolomorphicAt (localPullbackAt h hf ω x hx) (f x) := by
  classical
  set z₀ : ℂ := chartAt ℂ x x with hz₀_def
  set w₀ : ℂ := chartAt ℂ (f x) (f x) with hw₀_def
  set F : ℂ → ℂ := chartLocalAt f x with hF_def
  have hfHolAt : IsHolomorphicAt f x := hf.holomorphicAt x
  have hF_an : AnalyticAt ℂ F z₀ := hfHolAt
  have hFz₀ : F z₀ = w₀ := by simp [F, z₀, w₀, chartLocalAt]
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
  have hr_tendsto : Filter.Tendsto r (𝓝 w₀) (𝓝 z₀) := by
    have := hr_an_at_w₀.continuousAt
    rwa [ContinuousAt, hr_w₀] at this
  have h_chartXsymm_z₀ : (chartAt ℂ x).symm z₀ = x := by
    simp [z₀, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
  have h_chartYsymm_w₀ : (chartAt ℂ (f x)).symm w₀ = f x := by
    simp [w₀, (chartAt ℂ (f x)).left_inv (mem_chart_source ℂ (f x))]
  have h_chartXsymm_tendsto : Filter.Tendsto (fun z : ℂ => (chartAt ℂ x).symm z)
      (𝓝 z₀) (𝓝 x) := by
    have hcont := (chartAt ℂ x).continuousAt_symm
      ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
    change Filter.Tendsto (fun z => (chartAt ℂ x).symm z) (𝓝 z₀)
      (𝓝 ((chartAt ℂ x).symm z₀)) at hcont
    rwa [h_chartXsymm_z₀] at hcont
  have h_chartYsymm_tendsto : Filter.Tendsto (fun z : ℂ => (chartAt ℂ (f x)).symm z)
      (𝓝 w₀) (𝓝 (f x)) := by
    have hcont := (chartAt ℂ (f x)).continuousAt_symm
      ((chartAt ℂ (f x)).map_source (mem_chart_source ℂ (f x)))
    change Filter.Tendsto (fun z => (chartAt ℂ (f x)).symm z) (𝓝 w₀)
      (𝓝 ((chartAt ℂ (f x)).symm w₀)) at hcont
    rwa [h_chartYsymm_w₀] at hcont
  have h_anal_inv_tendsto : Filter.Tendsto (fun z : ℂ => (chartAt ℂ x).symm (r z))
      (𝓝 w₀) (𝓝 x) := h_chartXsymm_tendsto.comp hr_tendsto
  obtain ⟨U, V, hUopen, hVopen, hxU, hfxV, hbij, hright_branch, hleft_branch⟩ :=
    h.localInverse_is_inverse hx
  have h_y'_in_V : ∀ᶠ z in 𝓝 w₀, (chartAt ℂ (f x)).symm z ∈ V :=
    h_chartYsymm_tendsto.eventually (hVopen.mem_nhds hfxV)
  have h_anal_inv_in_U : ∀ᶠ z in 𝓝 w₀, (chartAt ℂ x).symm (r z) ∈ U :=
    h_anal_inv_tendsto.eventually (hUopen.mem_nhds hxU)
  have h_anal_inv_in_chart_source : ∀ᶠ z in 𝓝 w₀,
      (chartAt ℂ x).symm (r z) ∈ (chartAt ℂ x).source :=
    h_anal_inv_tendsto.eventually
      ((chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x))
  have h_localInv_eq : ∀ᶠ z in 𝓝 w₀,
      h.localInverseAt x hx ((chartAt ℂ (f x)).symm z) =
        (chartAt ℂ x).symm (r z) := by
    have h_f_anal_inv_in_src : ∀ᶠ z in 𝓝 w₀,
        f ((chartAt ℂ x).symm (r z)) ∈ (chartAt ℂ (f x)).source := by
      have htendsto : Filter.Tendsto (fun z => f ((chartAt ℂ x).symm (r z))) (𝓝 w₀)
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
  set Θ : ℂ → ℂ := fun ε => (ω.toFun ((chartAt ℂ x).symm ε)) (1 : ℂ) with hΘ_def
  have hΘ_an : AnalyticAt ℂ Θ z₀ := by
    simpa [Θ, z₀] using etaTimesOne_chart_local_analytic ω x
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
  unfold IsHolomorphicAt chartLocalAt
  refine h_chartCand_an.congr ?_
  have h_evt_unram : ∀ᶠ z in 𝓝 w₀,
      h.ramificationIndex (h.localInverseAt x hx ((chartAt ℂ (f x)).symm z)) = 1 :=
    h_chartYsymm_tendsto.eventually
      (h.localInverseAt_eventually_unramified x hx)
  have h_z_in_target_evt : ∀ᶠ z in 𝓝 w₀, z ∈ (chartAt ℂ (f x)).target :=
    chart_target_mem_nhds ℂ (f x)
  have h_rz_in_target_evt : ∀ᶠ z in 𝓝 w₀, r z ∈ (chartAt ℂ x).target := by
    have h_z₀_in_target : z₀ ∈ (chartAt ℂ x).target := by
      show chartAt ℂ x x ∈ (chartAt ℂ x).target
      exact (chartAt ℂ x).map_source (mem_chart_source ℂ x)
    exact hr_tendsto.eventually ((chartAt ℂ x).open_target.mem_nhds h_z₀_in_target)
  filter_upwards [h_localInv_eq, h_evt_unram, h_anal_inv_in_chart_source,
    h_y'_in_V, h_z_in_target_evt, h_rz_in_target_evt]
    with z h_loc_eq h_unram h_anal_in_src h_y_in_V h_z_in_target h_rz_in_target
  set y' : Y := (chartAt ℂ (f x)).symm z with hy'_def
  set x' : X := h.localInverseAt x hx y' with hx'_def
  have hx'_alt : x' = (chartAt ℂ x).symm (r z) := h_loc_eq
  have h_chart_eq : chartAt ℂ x' = chartAt ℂ x :=
    JacobianChallenge.Periods.StableChartAt.chartAt_eq_of_mem_source
      x x' (by rw [hx'_alt]; exact h_anal_in_src)
  have h_chartAt_x'_x' : chartAt ℂ x' x' = r z := by
    rw [h_chart_eq, hx'_alt]
    exact (chartAt ℂ x).right_inv h_rz_in_target
  have hfx'_eq_y' : f x' = (chartAt ℂ (f x)).symm z := by
    show f (h.localInverseAt x hx y') = (chartAt ℂ (f x)).symm z
    exact hright_branch y' h_y_in_V
  have h_fx'_in_chartY_source : f x' ∈ (chartAt ℂ (f x)).source := by
    rw [hfx'_eq_y']
    exact (chartAt ℂ (f x)).map_target h_z_in_target
  have h_chartY_eq : chartAt ℂ (f x') = chartAt ℂ (f x) :=
    JacobianChallenge.Periods.StableChartAt.chartAt_eq_of_mem_source
      (f x) (f x') h_fx'_in_chartY_source
  have h_chartLocalAt_eq : chartLocalAt f x' = F := by
    show chartAt ℂ (f x') ∘ f ∘ (chartAt ℂ x').symm = chartLocalAt f x
    rw [h_chartY_eq, h_chart_eq]
    rfl
  have h_cp_apply :=
    cotangentPushforward_apply_one (f := f) h hcompat hf (x := x') h_unram (ω.toFun x')
  have h_eta_eq : (ω.toFun x') (1 : ℂ) = Θ (r z) := by
    show (ω.toFun x') (1 : ℂ) = (ω.toFun ((chartAt ℂ x).symm (r z))) (1 : ℂ)
    rw [hx'_alt]
  symm
  show (chartAt ℂ (localPullbackAt h hf ω x hx (f x))
      (localPullbackAt h hf ω x hx ((chartAt ℂ (f x)).symm z)))
    = (deriv F (r z))⁻¹ * Θ (r z)
  show (chartAt ℂ (localPullbackAt h hf ω x hx (f x))
      (cotangentPushforward f x' (ω.toFun x')))
    = (deriv F (r z))⁻¹ * Θ (r z)
  have h_chart_eq_iso : (chartAt ℂ (localPullbackAt h hf ω x hx (f x))
      (cotangentPushforward f x' (ω.toFun x')))
    = (cotangentPushforward f x' (ω.toFun x')) (1 : ℂ) := rfl
  rw [h_chart_eq_iso, h_cp_apply, h_chartLocalAt_eq, h_chartAt_x'_x', h_eta_eq]
  rfl

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
    simp only [Function.comp_def]
    exact analyticAt_const
  · intro a s ha ih hfs
    have ha_holo : IsHolomorphicAt (f a) p :=
      hfs a (Finset.mem_insert_self a s)
    have hs_holo : IsHolomorphicAt (fun y => Finset.sum s (fun i => f i y)) p :=
      ih fun i hi => hfs i (Finset.mem_insert_of_mem hi)
    unfold IsHolomorphicAt chartLocalAt at *
    have hsum := ha_holo.add hs_holo
    simp only [Function.comp_def, Finset.sum_insert ha]
    exact hsum

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
    [T2Space X] [T2Space Y]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [JacobianChallenge.Periods.StableChartAt ℂ Y]
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
