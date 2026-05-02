import Jacobian.HolomorphicForms.VanishingOrder
import Mathlib.Analysis.Analytic.Order

/-!
# Holomorphic maps between charted-on-`ℂ` spaces

A project-local definition of "holomorphic at a point" / "holomorphic"
for maps `f : X → Y` between two `ChartedSpace ℂ`-equipped spaces.
Mathlib `v4.28.0` does not provide a manifold-level analytic predicate
(no `MAnalyticAt`, no `Holomorphic*`), so we roll our own using the
canonical chart `chartAt ℂ` on each side and Mathlib's
`AnalyticAt ℂ` for the chart-local expression.

This is the first piece of the bridge from Mathlib's `ℂ → ℂ` analytic
infrastructure to the analytic constructor
`branchedCoverData_of_nonconstant_holomorphic` in
`Jacobian/Blueprint/Sec02/BranchedDegree.lean` (the still-`sorry`-bearing
"leaf 8" of the branched-degree story).

## Main definitions

* `chartLocalAt f p` : the chart-local presentation
  `chartAt ℂ (f p) ∘ f ∘ (chartAt ℂ p).symm : ℂ → ℂ`.  This is the
  function whose analyticity / power-series order encode the analytic
  behaviour of `f` near `p`.
* `IsHolomorphicAt f p` : `f` is holomorphic at `p`, i.e. the
  chart-local presentation is `AnalyticAt ℂ` at `chartAt ℂ p p`.
* `IsHolomorphic f` : `f` is continuous and holomorphic at every point.
* `mapAnalyticOrderAt f p` : chart-local ramification / multiplicity
  index of `f` at `p`.  Defined as
  `analyticOrderNatAt (chartLocalAt f p · - chartLocalAt f p (chartAt ℂ p p)) (chartAt ℂ p p)`.

## Reuse of project infrastructure

The chart-transition machinery already discharged in
`Jacobian/HolomorphicForms/VanishingOrder.lean`
(`analyticAt_transition_of_mem_maximalAtlas`,
`transition_analyticAt`, `transition_deriv_ne_zero`,
`orderAt_eq_meromorphicOrderAt_of_mem_maximalAtlas`) carries over to
the holomorphic-map setting.  Future expansions of this file will lift
those theorems to chart-independence statements for `IsHolomorphicAt`
and `mapAnalyticOrderAt`.
-/

namespace JacobianChallenge.HolomorphicForms.HolomorphicMap

open scoped Manifold Topology ContDiff
open Set Filter

variable {X Y : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-- Canonical chart-local presentation of `f : X → Y` at `p`:
the function `t ↦ chartAt ℂ (f p) (f (chartAt ℂ p).symm t)` from `ℂ` to
`ℂ`.  Defined only via the canonical charts, hence does not require
`IsManifold`. -/
noncomputable def chartLocalAt (f : X → Y) (p : X) : ℂ → ℂ :=
  chartAt ℂ (f p) ∘ f ∘ (chartAt ℂ p).symm

/-- `f : X → Y` is *holomorphic at* `p` iff its canonical chart-local
presentation is analytic at `chartAt ℂ p p` in the usual `ℂ → ℂ` sense.

Definition uses only the canonical charts at `p` and `f p`; chart
independence (over the maximal atlas) is a separate theorem to be
proved using `analyticAt_transition_of_mem_maximalAtlas` from
`Jacobian.HolomorphicForms.VanishingOrder`. -/
def IsHolomorphicAt (f : X → Y) (p : X) : Prop :=
  AnalyticAt ℂ (chartLocalAt f p) (chartAt ℂ p p)

/-- `f : X → Y` is *holomorphic* iff it is continuous and holomorphic
at every point.  Continuity is included so that consumers of the
predicate can talk about `f ⁻¹' {y}` and pull back open sets without
re-deriving continuity from chart-local analyticity. -/
structure IsHolomorphic (f : X → Y) : Prop where
  /-- Holomorphic maps are continuous. -/
  continuous : Continuous f
  /-- Holomorphic at every point. -/
  holomorphicAt : ∀ p, IsHolomorphicAt f p

/-- The *chart-local order of vanishing* of `f - f p` at `p`, computed
in the canonical chart pair.  Concretely:

  `mapAnalyticOrderAt f p = analyticOrderNatAt (Δ_p f) (chartAt ℂ p p)`

where `Δ_p f t = chartLocalAt f p t - chartLocalAt f p (chartAt ℂ p p)`
is the chart-local presentation centred on its value at `chartAt ℂ p p`.

Returns `0` if `f` is not analytic at `p` (`AnalyticOrderNatAt` falls
through to `0`) or if the chart-local difference is non-zero at
`chartAt ℂ p p` (which cannot happen by construction — it always
vanishes there — but is recorded as a junk default).  For a holomorphic
non-locally-constant map the value is `≥ 1`; this is the analytic input
to `BranchedCoverData.ramificationIndex_pos`. -/
noncomputable def mapAnalyticOrderAt (f : X → Y) (p : X) : ℕ :=
  analyticOrderNatAt
    (fun t => chartLocalAt f p t - chartLocalAt f p (chartAt ℂ p p))
    (chartAt ℂ p p)

/-- The chart-local difference function used in `mapAnalyticOrderAt`
vanishes at the chart image of `p`.  This is a definitional fact about
`chartLocalAt` and centring. -/
@[simp]
theorem chartLocal_diff_self (f : X → Y) (p : X) :
    (fun t => chartLocalAt f p t - chartLocalAt f p (chartAt ℂ p p))
      (chartAt ℂ p p) = 0 := by
  simp

end JacobianChallenge.HolomorphicForms.HolomorphicMap
