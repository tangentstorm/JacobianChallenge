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

/-- The local inverse is holomorphic at `f x`.

BLOCKER (2026-05-12): this theorem is currently blocked on several missing
prerequisites that cannot be addressed inside this file under the allowed
write scope.

1. **Definitional inconsistency in `localInverseAt`.** The body of
   `localInverseAt` uses `hbij.invOn.f' y`, but neither `Set.BijOn.invOn`
   nor `Set.InvOn` exposes a field `.f'` on the pinned Mathlib commit.
   The canonical noncomputable left/right inverse for a `Set.BijOn` is
   `Function.invFunOn f U`.  Until `localInverseAt` is rewritten to use a
   well-defined inverse (e.g. `Function.invFunOn f U y` or the analytic
   local inverse produced by `AnalyticAt.localInverse`), the statement
   here has no provable content.  Fixing this requires editing the
   `localInverseAt` definition above, which is allowed by scope, but the
   correct replacement is itself dictated by item (3) below.

2. **No analytic content in `BranchedCoverData.ramificationIndex`.**
   The structure field `ramificationIndex : X → ℕ` is abstract data:
   nothing in `BranchedCoverData` ties it to `mapAnalyticOrderAt f x` or
   to nonvanishing of the chart-local derivative.  To turn
   `h.ramificationIndex x = 1` into "the chart-local derivative of `f` at
   `chartAt ℂ x x` is nonzero", we need either a compatibility lemma
   `h.ramificationIndex x = mapAnalyticOrderAt f x` (currently absent
   from `BranchedCover.lean`) or a separate hypothesis carrying that
   information.

3. **`AnalyticAt.localInverse` API at the manifold level.** Mathlib
   v4.28.0 provides `AnalyticAt.localInverse` for `ℂ → ℂ` analytic
   functions with nonzero derivative, but no manifold-level
   `IsHolomorphicAt.localInverse`.  Lifting the chart-local analytic
   inverse to `IsHolomorphicAt` on the manifold requires showing that
   the lifted function coincides with `localInverseAt h x hx` on a
   neighbourhood of `f x` and then invoking
   `IsHolomorphicAt.congr_of_eventuallyEq` (also currently absent from
   `HolomorphicMap.lean`).

The intended three-step proof remains:
1. Order = 1 implies chart-local derivative is nonzero.
2. Apply `AnalyticAt.localInverse` from Mathlib.
3. Transport holomorphicity back to the manifold side.
-/
theorem localInverseAt_holomorphic
    {f : X → Y} (h : BranchedCoverData X Y f)
    (hf : IsHolomorphic f)
    (x : X) (hx : h.ramificationIndex x = 1) :
    IsHolomorphicAt (localInverseAt h x hx) (f x) := by
  -- BLOCKER: see the docstring above.  Prerequisites missing:
  --   * `localInverseAt` uses an undefined `.f'` projection.
  --   * `BranchedCoverData.ramificationIndex` is not linked to
  --     `mapAnalyticOrderAt f` (no compatibility lemma).
  --   * No manifold-level `AnalyticAt.localInverse` / no
  --     `IsHolomorphicAt.congr_of_eventuallyEq` in `HolomorphicMap.lean`.
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
(tr f (f* η))_y = deg(f) • η_y.

BLOCKER (2026-05-12): this theorem is currently blocked on the same missing
prerequisite documented at `localInverseAt_holomorphic` (item 2 of its
docstring): there is no link between `BranchedCoverData.ramificationIndex`
and the analytic content of the manifold differential `mfderiv`.

The intended four-step reduction is:

1. Pullback definition: `(pullbackFormsBundled f _ η).toFun x` unfolds to
   `pullbackFormsFunFiber f η x = (η.toFun (f x)).comp (mfderiv 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) f x)`.
2. For `x ∈ f ⁻¹' {y}`, rewrite `f x = y` so the term reads
   `(η.toFun y).comp (mfderiv 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) f x)`.
3. Apply `cotangentPushforward` with `IsIso (mfderiv 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) f x)`:
   the inverse cancels the chain-rule factor and the summand reduces to
   `η.toFun y` (using `ContinuousLinearMap.comp_assoc`,
   `IsIso.right_inv`, and `ContinuousLinearMap.comp_id`).
4. The sum over the (unramified) fiber becomes
   `(h.finite_fiber y).toFinset.card • η.toFun y`, which equals
   `(h.weightedFiberCard y : ℂ) • η.toFun y` because every summand of the
   weighted count is `1` at a regular value (see
   `branchedDegree_eq_card_toFinset_of_unramified_fiber` for the integer
   analogue).

**Missing prerequisite.** Step 3 requires
`IsIso (mfderiv 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) f x)` for every `x` in the regular fiber.
`BranchedCoverData.ramificationIndex : X → ℕ` is abstract data — nothing
in `BranchedCoverData` ties it to `mapAnalyticOrderAt f x` or to
nonvanishing of the chart-local derivative. To turn
`h.ramificationIndex x = 1` into `IsIso (mfderiv … f x)` we need either:

* a compatibility lemma `h.ramificationIndex x = mapAnalyticOrderAt f x`
  (currently absent from `BranchedCover.lean`) plus the analytic-order-one
  ⇒ derivative-nonzero bridge, transported across charts, or
* a new structure field on `BranchedCoverData` recording the analytic
  identification (and consequently a refactor of every existing producer
  of `BranchedCoverData`), or
* a separate hypothesis on `trace_pullback_at_regular_value` carrying the
  IsIso witness, taken as input.

Editing `BranchedCoverData` or weakening the theorem statement is out of
scope here (forbidden writes); naming the prerequisite is the correct
action under the project's BLOCKER convention.

A secondary technical point: the `sorry` appearing inside the statement
(as the `hf` argument to `pullbackFormsBundled`) is harmless for the
present blocker analysis, because `pullbackFormsBundled.toFun` reduces
to `pullbackFormsFunFiber` independent of the smoothness witness.
Discharging this `sorry` would require carrying a `ContMDiff` hypothesis
on `f`; this is a separate concern from the IsIso blocker above. -/
theorem trace_pullback_at_regular_value
    {f : X → Y} (h : BranchedCoverData X Y f)
    (η : HolomorphicOneForm ℂ Y)
    (y : Y) (hy : isRegularValue h y) :
    traceAtRegularValue h (fun x => (pullbackFormsBundled f sorry η).toFun x) y hy =
      (h.weightedFiberCard y : ℂ) • η.toFun y := by
  -- BLOCKER: see the docstring above.  The reduction requires
  --   `IsIso (mfderiv 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) f x)` for every `x` in the regular
  --   fiber, but `h.ramificationIndex x = 1` carries no analytic content
  --   linking it to `mfderiv`.  Same missing prerequisite as
  --   `localInverseAt_holomorphic` (item 2 of its BLOCKER docstring).
  sorry

end JacobianChallenge.HolomorphicForms
