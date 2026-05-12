import Jacobian.HolomorphicForms.BranchedCover
import Jacobian.HolomorphicForms.CotangentBundle
import Jacobian.HolomorphicForms.PullbackBundled
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Algebra.Module.Equiv

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

open scoped Manifold Topology
open JacobianChallenge.HolomorphicForms
open JacobianChallenge.HolomorphicForms.HolomorphicMap

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
Given $f : X \to Y$ and $x$ such that $df_x$ is an isomorphism,
we push $\omega_x \in T_x^* X$ to $T_{f(x)}^* Y$. -/
noncomputable def cotangentPushforward
    (f : X → Y) (x : X) (ωx : CotangentSpace ℂ X x) :
    CotangentSpace ℂ Y (f x) :=
  let df := mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x
  -- At regular values, df is a continuous linear equivalence.
  -- For the top-down refinement, we use the inverse if it exists.
  if h : Nonempty (IsIso df) then
    ωx.comp (Classical.choice h).inv
  else
    0

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

/-- **Plan leaf 14 (NEW).** The local inverse is holomorphic at `f x`.
Proved by bridging the combinatorial `h.localInverseAt` to the analytic
`hf.localInverse` on a neighborhood of `f x`. -/
theorem localInverseAt_holomorphic
    {f : X → Y} (h : BranchedCoverData X Y f)
    (hf : IsHolomorphic f)
    (x : X) (hx : h.ramificationIndex x = 1) :
    IsHolomorphicAt (h.localInverseAt x hx) (f x) := by
  -- 1. Combinatorial order 1 implies analytic order 1.
  have hram : mapAnalyticOrderAt f x = 1 := by
    rw [← h.ramificationIndex_eq_mapAnalyticOrderAt (hf.holomorphicAt x)]
    exact hx
  -- 2. Analytic order 1 implies nonzero derivative.
  have hderiv : deriv (chartLocalAt f x) (chartAt ℂ x x) ≠ 0 := by
    -- mapAnalyticOrderAt f x = 1 implies deriv ≠ 0
    sorry
  -- 3. The combinatorial and analytic inverses agree eventually.
  have h_agree : h.localInverseAt x hx =ᶠ[𝓝 (f x)] (hf.holomorphicAt x).localInverse hderiv := by
    sorry
  -- 4. Apply holomorphicity of the analytic inverse + congruence.
  refine IsHolomorphicAt.congr_of_eventuallyEq ?_ h_agree.symm
  exact (hf.holomorphicAt x).localInverse_isHolomorphicAt hderiv

/-- The pullback of a holomorphic form along a local inverse branch.
Underlying function: `y' ↦ (df_{s_i(y')})⁻¹* ω_{s_i(y')}`. -/
noncomputable def localPullbackAt
    {f : X → Y} (h : BranchedCoverData X Y f)
    (hf : IsHolomorphic f)
    (ω : HolomorphicOneForm ℂ X)
    (x : X) (hx : h.ramificationIndex x = 1) :
    Y → CotangentModelFiber ℂ :=
  -- Use localInverseAt and cotangentPushforward
  fun y => cotangentPushforward f (h.localInverseAt x hx y) (ω (h.localInverseAt x hx y))

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

/-! ### Local infrastructure for `localTraceAtRegularValue_holomorphic`

The trace is a `Finset.sum` of `Y → CotangentModelFiber ℂ` valued
functions, so to prove `IsHolomorphicAt (... sum ...) y` we need:

1. a `ChartedSpace ℂ (CotangentModelFiber ℂ)` instance so the conclusion
   `IsHolomorphicAt _ y` even elaborates (the target type
   `CotangentModelFiber ℂ = ℂ →L[ℂ] ℂ` has no native instance — Mathlib
   gives only `chartedSpaceSelf (ℂ →L[ℂ] ℂ)`, which uses the wrong
   model);
2. closure of `IsHolomorphicAt` under finite sums (zero summand + cons
   summand) for cotangent-fibre targets;
3. holomorphicity of each summand `localPullbackAt h hf ω x hx` at `y`,
   which combines `localInverseAt_holomorphic` (now available upstream
   modulo two sub-`sorry`s) with holomorphicity of the cotangent
   pushforward in its base argument.

The pieces below are stated in the form needed for the main theorem.
-/

/-- Evaluation at `1` gives a continuous ℂ-linear equivalence
`(ℂ →L[ℂ] ℂ) ≃L[ℂ] ℂ`.  Used to install a `ChartedSpace ℂ` structure on
`CotangentModelFiber ℂ`. -/
noncomputable def cotangentFiberEquivℂ : (ℂ →L[ℂ] ℂ) ≃L[ℂ] ℂ where
  toFun f := f 1
  invFun c := ContinuousLinearMap.toSpanSingleton ℂ c
  left_inv f := by
    ext x
    have hx : x = x • (1 : ℂ) := by rw [smul_eq_mul, mul_one]
    calc (ContinuousLinearMap.toSpanSingleton ℂ (f 1)) x
        = x • f 1 := by simp [ContinuousLinearMap.toSpanSingleton_apply]
      _ = f (x • 1) := (f.map_smul x 1).symm
      _ = f x := by rw [smul_eq_mul, mul_one]
  right_inv c := by simp [ContinuousLinearMap.toSpanSingleton_apply]
  map_add' f g := by simp
  map_smul' c f := by simp
  continuous_toFun :=
    (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).continuous
  continuous_invFun := by
    simpa using (ContinuousLinearMap.toSpanSingleton ℂ
      (M := ℂ) (E := ℂ)).continuous

/-- Single chart for `CotangentModelFiber ℂ` provided by
`cotangentFiberEquivℂ`. -/
noncomputable def cotangentFiberChart :
    PartialHomeomorph (CotangentModelFiber ℂ) ℂ :=
  cotangentFiberEquivℂ.toHomeomorph.toPartialHomeomorph

@[simp] theorem cotangentFiberChart_source :
    cotangentFiberChart.source = Set.univ := by
  simp [cotangentFiberChart]

@[simp] theorem cotangentFiberChart_target :
    cotangentFiberChart.target = Set.univ := by
  simp [cotangentFiberChart]

/-- Single-chart `ChartedSpace ℂ (CotangentModelFiber ℂ)` instance via
the canonical evaluation isomorphism. -/
noncomputable instance : ChartedSpace ℂ (CotangentModelFiber ℂ) where
  atlas := {cotangentFiberChart}
  chartAt _ := cotangentFiberChart
  mem_chart_source _ := by simp
  chart_mem_atlas _ := rfl

@[simp] theorem chartAt_cotangentModelFiber (v : CotangentModelFiber ℂ) :
    (chartAt ℂ v : PartialHomeomorph (CotangentModelFiber ℂ) ℂ) =
      cotangentFiberChart := rfl

@[simp] theorem cotangentFiberChart_apply (v : CotangentModelFiber ℂ) :
    cotangentFiberChart v = v 1 := rfl

@[simp] theorem cotangentFiberChart_symm_apply (c : ℂ) :
    cotangentFiberChart.symm c = ContinuousLinearMap.toSpanSingleton ℂ c :=
  rfl

/-- The constant zero function `Y → CotangentModelFiber ℂ` is
holomorphic at any point. -/
theorem isHolomorphicAt_const_zero (y : Y) :
    IsHolomorphicAt (fun _ : Y => (0 : CotangentModelFiber ℂ)) y := by
  -- Chart-local presentation is the constant `0 : ℂ`, which is analytic.
  show AnalyticAt ℂ (chartLocalAt (fun _ : Y => (0 : CotangentModelFiber ℂ)) y)
      (chartAt ℂ y y)
  refine analyticAt_const.congr ?_
  filter_upwards with t
  simp [chartLocalAt, cotangentFiberChart, cotangentFiberEquivℂ]

/-- `IsHolomorphicAt` on `Y → CotangentModelFiber ℂ` is closed under
pointwise addition. -/
theorem IsHolomorphicAt.add_cotangent
    {g₁ g₂ : Y → CotangentModelFiber ℂ} {y : Y}
    (hg₁ : IsHolomorphicAt g₁ y) (hg₂ : IsHolomorphicAt g₂ y) :
    IsHolomorphicAt (fun y' => g₁ y' + g₂ y') y := by
  -- The chart-local presentation is linear in the cotangent-fibre
  -- coordinate (evaluation at `1`), so addition passes through.
  show AnalyticAt ℂ
    (chartLocalAt (fun y' => g₁ y' + g₂ y') y) (chartAt ℂ y y)
  have hsum : chartLocalAt (fun y' => g₁ y' + g₂ y') y
      = chartLocalAt g₁ y + chartLocalAt g₂ y := by
    funext t
    simp [chartLocalAt, cotangentFiberChart, cotangentFiberEquivℂ,
      ContinuousLinearMap.add_apply]
  rw [hsum]
  exact hg₁.add hg₂

/-- `IsHolomorphicAt` on `Y → CotangentModelFiber ℂ` is closed under
finite `Finset.sum`. -/
theorem isHolomorphicAt_finset_sum
    {ι : Type*} (s : Finset ι) (g : ι → Y → CotangentModelFiber ℂ)
    (y : Y) (hg : ∀ i ∈ s, IsHolomorphicAt (g i) y) :
    IsHolomorphicAt (fun y' => ∑ i ∈ s, g i y') y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using isHolomorphicAt_const_zero (Y := Y) y
  | insert a s has ih =>
      have h_a : IsHolomorphicAt (g a) y := hg a (Finset.mem_insert_self _ _)
      have h_s : IsHolomorphicAt (fun y' => ∑ i ∈ s, g i y') y :=
        ih (fun i hi => hg i (Finset.mem_insert_of_mem hi))
      have hsum_eq :
          (fun y' => ∑ i ∈ insert a s, g i y') =
            (fun y' => g a y' + ∑ i ∈ s, g i y') := by
        funext y'
        exact Finset.sum_insert has
      rw [hsum_eq]
      exact h_a.add_cotangent h_s

/-- Holomorphicity of `localPullbackAt h hf ω x hx` at `y = f x`.

The pullback is `y' ↦ cotangentPushforward f (s y') (ω (s y'))` with
`s := h.localInverseAt x hx`.  Holomorphicity follows from:
`s` is holomorphic at `f x` (by `localInverseAt_holomorphic`), `ω` is a
holomorphic 1-form (its chart-local coefficient is analytic), and the
cotangent pushforward in the chart-local presentation reduces to
division by the nonvanishing chart-local derivative of `f` at `s y'`.

This intermediate step still needs the cotangent-pushforward chart
identity; we record it as an obligation here for the next pass. -/
theorem localPullbackAt_holomorphicAt
    {f : X → Y} (h : BranchedCoverData X Y f) (hf : IsHolomorphic f)
    (ω : HolomorphicOneForm ℂ X) {x : X} (hx : h.ramificationIndex x = 1) :
    IsHolomorphicAt (localPullbackAt h hf ω x hx) (f x) := by
  -- The proof reduces to:
  --   * `localInverseAt_holomorphic h hf x hx : IsHolomorphicAt _ (f x)`
  --     (in `Jacobian/TraceDegree/TraceDefinition.lean`, modulo two
  --     internal sub-`sorry`s on `deriv ≠ 0` and `=ᶠ`),
  --   * `cotangentPushforward` chart identity:
  --     `cotangentFiberChart (cotangentPushforward f x' ω) =
  --       (1 / chartLocalDeriv f x') · cotangentFiberChart ω`
  --     (this identity is not yet anywhere in the project).
  -- Until that chart identity exists, no compiling proof is possible
  -- here without a placeholder.
  sorry

/-- The local trace is holomorphic at regular values.

Strategy:

1. The trace `localTraceAtRegularValue h hf ω y hy` is a finite
   `Finset.sum` over the fibre `f⁻¹{y}` of pullbacks `localPullbackAt`.
2. Each pullback is holomorphic at `y` by `localPullbackAt_holomorphicAt`
   (using `f x = y` for `x ∈ f⁻¹{y}`).
3. Finite sums of holomorphic functions are holomorphic by
   `isHolomorphicAt_finset_sum`. -/
theorem localTraceAtRegularValue_holomorphic
    {f : X → Y} (h : BranchedCoverData X Y f)
    (hf : IsHolomorphic f)
    (ω : HolomorphicOneForm ℂ X)
    (y : Y) (hy : isRegularValue h y) :
    IsHolomorphicAt (localTraceAtRegularValue h hf ω y hy) y := by
  unfold localTraceAtRegularValue
  -- Reduce to a finite-sum-of-holomorphic claim, indexed by
  -- `((h.finite_fiber y).toFinset).attach`.
  refine isHolomorphicAt_finset_sum
    ((h.finite_fiber y).toFinset.attach)
    (fun a y' =>
      localPullbackAt h hf ω a.1
        (hy a.1 ((Set.Finite.mem_toFinset _).mp a.2)) y')
    y ?_
  -- Per-fibre obligation: each pullback is holomorphic at `y`.
  intro a _ha_mem
  have hx_fiber : a.1 ∈ f ⁻¹' {y} :=
    (Set.Finite.mem_toFinset _).mp a.2
  have hf_a : f a.1 = y := hx_fiber
  -- Transport `f a.1 = y` through the pullback-holomorphic lemma.
  have :=
    localPullbackAt_holomorphicAt h hf ω
      (hy a.1 hx_fiber)
  -- `localPullbackAt_holomorphicAt` concludes at `f a.1`; rewrite to `y`.
  simpa [hf_a] using this

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
