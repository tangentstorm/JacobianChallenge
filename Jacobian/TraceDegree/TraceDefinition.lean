import Jacobian.HolomorphicForms.BranchedCover
import Jacobian.HolomorphicForms.CotangentBundle
import Jacobian.HolomorphicForms.PullbackBundled

/-!
# Trace (pushforward) of differential forms along a branched cover

This file defines the trace (pushforward) of differential 1-forms along
a branched cover `f : X → Y`.

The trace `f_* ω` for a 1-form `ω` on `X` is defined at a regular value `y ∈ Y`
by summing the pullbacks of `ω` along the local inverse branches of `f`:
`(f_* ω)_y = ∑_{x ∈ f⁻¹(y)} (f_x⁻¹)⁻¹* ω_x`
where `f_x` is a local diffeomorphism at `x`.

## Main definitions

* `regularValue f h` — the set of values `y : Y` such that all preimages
  of `y` are unramified.
* `traceFormsFun f h ω` — the trace of a 1-form `ω` as a function
  defined on the regular locus of `f`.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open JacobianChallenge.HolomorphicForms
open JacobianChallenge.HolomorphicForms.HolomorphicMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
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

/-- The pushforward of a cotangent vector along a local diffeomorphism.
Given $f : X \to Y$ and $x$ such that $df_x$ is an isomorphism,
we push $\omega_x \in T_x^* X$ to $T_{f(x)}^* Y$. -/
noncomputable def cotangentPushforward
    (f : X → Y) (x : X) (ωx : CotangentSpace ℂ X x) :
    CotangentSpace ℂ Y (f x) :=
  let df := mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x
  -- At regular values, df is a continuous linear equivalence.
  -- For the top-down refinement, we use the inverse if it exists.
  if h : IsIso df then
    ωx.comp h.inv
  else
    0

/-- Predicate for a continuous linear map being an isomorphism. -/
structure IsIso {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (f : E →L[ℂ] F) : Prop where
  inv : F →L[ℂ] E
  left_inv : inv.comp f = ContinuousLinearMap.id ℂ E
  right_inv : f.comp inv = ContinuousLinearMap.id ℂ F

/-- The trace of a 1-form at a regular value `y`.
Sum over $x \in f^{-1}(y)$ of $(df_x)^{-1*} \omega_x$. -/
noncomputable def traceAtRegularValue
    {f : X → Y} (h : BranchedCoverData X Y f)
    (ω : ∀ x, CotangentSpace ℂ X x)
    (y : Y) (hy : isRegularValue h y) : CotangentSpace ℂ Y y :=
  let fiber := (h.finite_fiber y).toFinset
  fiber.attach.sum (fun ⟨x, hx⟩ =>
    cotangentPushforward f x (ω x)
  )

/-- A local inverse of `f` at an unramified point `x`. -/
noncomputable def localInverseAt
    {f : X → Y} (h : BranchedCoverData X Y f)
    (x : X) (hx : h.ramificationIndex x = 1) :
    Y → X :=
  let ⟨_U, _V, _hU, _hV, _hxU, _hfxV, hbij⟩ := h.local_bijective_unramified x hx
  fun y => if hy : y ∈ _V then hbij.invOn.f' y else x

/-- The local inverse is holomorphic at `f x`. -/
theorem localInverseAt_holomorphic
    {f : X → Y} (h : BranchedCoverData X Y f)
    (hf : IsHolomorphic f)
    (x : X) (hx : h.ramificationIndex x = 1) :
    IsHolomorphicAt (localInverseAt h x hx) (f x) := by
  -- 1. Order = 1 implies chart-local derivative is nonzero.
  -- 2. Apply AnalyticAt.localInverse from Mathlib.
  -- 3. Transport holomorphicity back to the manifold side.
  sorry

/-- The pullback of a holomorphic form along a local inverse branch.
Underlying function: `y' ↦ (df_{s_i(y')})⁻¹* ω_{s_i(y')}`. -/
noncomputable def localPullbackAt
    {f : X → Y} (h : BranchedCoverData X Y f)
    (hf : IsHolomorphic f)
    (ω : HolomorphicOneForm ℂ X)
    (x : X) (hx : h.ramificationIndex x = 1) :
    Y → CotangentModelFiber ℂ :=
  -- Use localInverseAt and cotangentPushforward
  fun y => cotangentPushforward f (localInverseAt h x hx y) (ω (localInverseAt h x hx y))

/-- A local version of the trace sum, defined in a neighborhood of `y`.
Underlying function: `y' ↦ ∑ (df_{s_i(y')})⁻¹* ω_{s_i(y')}`. -/
noncomputable def localTraceAtRegularValue
    {f : X → Y} (h : BranchedCoverData X Y f)
    (hf : IsHolomorphic f)
    (ω : HolomorphicOneForm ℂ X)
    (y : Y) (hy : isRegularValue h y) :
    Y → CotangentModelFiber ℂ :=
  fun y' =>
    let fiber := (h.finite_fiber y).toFinset
    fiber.attach.sum (fun ⟨x, hx_mem⟩ =>
      let hx_fiber : x ∈ f ⁻¹' {y} := by
        rw [Set.Finite.mem_toFinset] at hx_mem
        assumption
      let hx_unram : h.ramificationIndex x = 1 := hy x hx_fiber
      localPullbackAt h hf ω x hx_unram y'
    )

/-- The local trace is holomorphic at regular values. -/
theorem localTraceAtRegularValue_holomorphic
    {f : X → Y} (h : BranchedCoverData X Y f)
    (hf : IsHolomorphic f)
    (ω : HolomorphicOneForm ℂ X)
    (y : Y) (hy : isRegularValue h y) :
    IsHolomorphicAt (localTraceAtRegularValue h hf ω y hy) y := by
  -- 1. Each term (pullback along local inverse) is holomorphic.
  -- 2. Finite sum of holomorphic functions is holomorphic.
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
  apply Finset.sum_congr rfl
  intro ⟨x, hx⟩ _
  unfold cotangentPushforward
  split_ifs with hiso
  · exact ContinuousLinearMap.add_comp _ _ _
  · rw [add_zero]; rfl

/-- The trace sum preserves scalar multiplication. -/
theorem traceAtRegularValue_smul
    {f : X → Y} (h : BranchedCoverData X Y f)
    (c : ℂ) (ω : ∀ x, CotangentSpace ℂ X x)
    (y : Y) (hy : isRegularValue h y) :
    traceAtRegularValue h (fun x => c • ω x) y hy =
      c • traceAtRegularValue h ω y hy := by
  unfold traceAtRegularValue
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro ⟨x, hx⟩ _
  unfold cotangentPushforward
  split_ifs with hiso
  · exact ContinuousLinearMap.smul_comp c _ _
  · rw [smul_zero]

/-- The trace of a pullback is scaled by the degree (at regular values).
(tr f (f* η))_y = deg(f) • η_y. -/
theorem trace_pullback_at_regular_value
    {f : X → Y} (h : BranchedCoverData X Y f)
    (η : HolomorphicOneForm ℂ Y)
    (y : Y) (hy : isRegularValue h y) :
    traceAtRegularValue h (fun x => (pullbackFormsBundled f sorry η).toFun x) y hy =
      (h.weightedFiberCard y : ℂ) • η.toFun y := by
  unfold traceAtRegularValue
  -- 1. Use pullback definition: (f* η)_x = η_{f(x)} ∘ df_x
  -- 2. Use cotangentPushforward definition: (df_x)⁻¹* (f* η)_x = η_{f(x)}
  -- 3. Sum over fiber: ∑ η_y = (card fiber) • η_y
  -- 4. weightedFiberCard = card fiber (since all e_x = 1)
  sorry

end JacobianChallenge.HolomorphicForms
