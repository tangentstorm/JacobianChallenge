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

/-- The local trace is holomorphic at regular values.

BLOCKED: this proof requires several prerequisites that are not yet
available in the project.

The function under analysis has type `Y → CotangentModelFiber ℂ`,
i.e. `Y → (ℂ →L[ℂ] ℂ)`, and the conclusion `IsHolomorphicAt _ y`
unfolds to `AnalyticAt ℂ (chartLocalAt _ y) (chartAt ℂ y y)` via the
project-local `JacobianChallenge.HolomorphicForms.HolomorphicMap`
definition.  Discharging this requires:

* **Missing prerequisite 1 — `ChartedSpace ℂ (CotangentModelFiber ℂ)`.**
  `IsHolomorphicAt` is currently defined only for maps `X → Y` between
  two `ChartedSpace ℂ`-equipped types.  The target
  `CotangentModelFiber ℂ = ℂ →L[ℂ] ℂ` has no such instance in scope:
  Mathlib only provides `chartedSpaceSelf` (giving
  `ChartedSpace (ℂ →L[ℂ] ℂ) (ℂ →L[ℂ] ℂ)`, not the required model on
  `ℂ`), and the project supplies no transitive instance.  Until either
  `IsHolomorphicAt` is generalised to allow normed-space valued maps
  (e.g. via `MAnalyticAt` / `ContMDiffAt` for a non-`ChartedSpace ℂ`
  codomain), or a `ChartedSpace ℂ (ℂ →L[ℂ] ℂ)` instance is built from
  the 1-dimensional evaluation isomorphism `(· 1) : (ℂ →L[ℂ] ℂ) ≃L[ℂ] ℂ`,
  the statement above does not have a usable elaboration target.

* **Missing prerequisite 2 — finite-sum closure for `IsHolomorphicAt`.**
  Even granting prerequisite 1, the trace is `Finset.sum`-shaped, so the
  proof needs `IsHolomorphicAt 0 y` (zero summand) and
  `IsHolomorphicAt.add` (cons summand) for the cotangent-fibre target.
  Neither lemma exists anywhere in `Jacobian/HolomorphicForms/`.

* **Missing prerequisite 3 — `localInverseAt_holomorphic`.**  Each
  summand is `cotangentPushforward f (localInverseAt h x hx y')
  (ω (localInverseAt h x hx y'))`; holomorphicity of every such summand
  reduces to holomorphicity of `localInverseAt h x hx` (the unproved
  `localInverseAt_holomorphic` `sorry` directly above) composed with the
  holomorphicity of `cotangentPushforward` in its base argument.

* **Missing prerequisite 4 — holomorphicity of `cotangentPushforward`
  in the base point.**  The definition contains an `if h : IsIso df
  then ωx.comp h.inv else 0` branch (with `IsIso` declared *after*
  `cotangentPushforward` in this very file, a forward reference that
  itself is suspicious).  No lemma states that `y' ↦
  cotangentPushforward f (s y') (ω (s y'))` is holomorphic when `s` is a
  local holomorphic section and `f` is unramified at `s y`, because the
  pushforward's `IsIso` branch is decided pointwise via `if … then …
  else 0` and the resulting function has no API connecting it to
  `IsHolomorphicAt` on `CotangentModelFiber ℂ`.

The proof skeleton, once those prerequisites are in place, is:

  1. `unfold localTraceAtRegularValue`.
  2. `apply Finset.holomorphicAt_sum` (the missing closure lemma) and
     reduce to a per-`x` goal.
  3. Each per-`x` goal is `IsHolomorphicAt (localPullbackAt h hf ω x
     hx_unram) y`, dispatched by composing
     `localInverseAt_holomorphic h hf x hx_unram` with the
     cotangent-pushforward holomorphicity lemma (also missing).

This file therefore leaves the statement unchanged and records the
blocker rather than introducing fake helper definitions.  -/
theorem localTraceAtRegularValue_holomorphic
    {f : X → Y} (h : BranchedCoverData X Y f)
    (hf : IsHolomorphic f)
    (ω : HolomorphicOneForm ℂ X)
    (y : Y) (hy : isRegularValue h y) :
    IsHolomorphicAt (localTraceAtRegularValue h hf ω y hy) y := by
  -- BLOCKER: see docstring above.  Missing prerequisites:
  --   1. `ChartedSpace ℂ (CotangentModelFiber ℂ)` instance (or a
  --      generalisation of `IsHolomorphicAt` to normed-space targets).
  --   2. Finite-sum closure lemmas
  --      (`IsHolomorphicAt 0`, `IsHolomorphicAt.add`) for that target.
  --   3. `localInverseAt_holomorphic` (also `sorry` above).
  --   4. Holomorphicity of `cotangentPushforward` in the base point.
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
