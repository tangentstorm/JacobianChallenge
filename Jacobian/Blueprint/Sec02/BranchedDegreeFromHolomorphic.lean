import Jacobian.Blueprint.Sec02.BranchedDegree
import Jacobian.HolomorphicForms.HolomorphicMap

/-! # Blueprint: `def:branched-degree`, leaf 8 — analytic constructor

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

Leaf 8 of the branched-degree story (`ref/plans/branched-degree.md`):
the *analytic* constructor producing a `BranchedCoverData X Y f` from
the analytic input "nonconstant holomorphic map between compact
connected Riemann surfaces".

This file is split out of `Sec02/BranchedDegree.lean` so the latter
can stay narrow (Finset / Set.Finite only) and so the manifold-level
analytic dependency is isolated to a single file.

## Status

The signature uses the project-local
`JacobianChallenge.HolomorphicForms.HolomorphicMap.IsHolomorphic`
predicate (see `Jacobian/HolomorphicForms/HolomorphicMap.lean`),
replacing the earlier `_hf : True` placeholder.  The body remains
`sorry`-bearing: discharging it requires three further analytic
ingredients that the project does not yet have:

1. **Chart-independence of `mapAnalyticOrderAt`** — needed to define
   `BranchedCoverData.ramificationIndex` independently of chart choice.
   Reduces to `analyticAt_transition_of_mem_maximalAtlas` (already
   discharged in `Jacobian/HolomorphicForms/VanishingOrder.lean`)
   plus an order-via-biholomorphic-substitution lemma.
2. **Finite fibres** — uses Mathlib's identity principle
   (`AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`)
   plus compactness of `X` to conclude that the zero set of
   `f - y₀` (locally) intersects every chart in a discrete set, hence
   the fibre is finite.
3. **Constancy of weighted fibre count
   (`weightedFiberCard_const`)** — the well-definedness of the degree.
   Standard proofs use either local triviality of branched coverings
   off the (finite) branch locus + a continuity argument across branch
   values, or homological / proper-degree machinery.  This is the
   single biggest analytic gap in the branched-degree story; it is
   genuinely several PRs of work and not a one-session item.

Until those three ingredients land, the body of the leaf-8 constructor
stays `sorry`.  The signature is now meaningful, however: any future
discharge will need a real `IsHolomorphic f` together with the
nonconstant hypothesis. -/

namespace JacobianChallenge.Blueprint

open JacobianChallenge.HolomorphicForms.HolomorphicMap

/-- **Plan leaf 8 (HARD, body `sorry`).** Analytic constructor for
`BranchedCoverData`: a holomorphic, non-locally-constant map
`f : X → Y` between two `ChartedSpace ℂ`-equipped spaces (with the
usual compact / Hausdorff / connected hypotheses on the topological
sides) packages as a branched-cover datum.

The "nonconstant" hypothesis here is stated as the absence of a
single `y₀` to which `f` sends every point: this is the weakest form
that still rules out the constant map and is what is actually needed
in the analytic-order calculations downstream.  A stronger form
("`f` is non-locally-constant near every `p`") would let us drop the
`ConnectedSpace X` hypothesis but is harder to use in practice.

The `IsHolomorphic f` hypothesis bundles continuity together with
chart-local analyticity at every point; see
`Jacobian/HolomorphicForms/HolomorphicMap.lean`. -/
noncomputable def branchedCoverData_of_nonconstant_holomorphic
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    [CompactSpace X] [T2Space X]
    [ConnectedSpace X] [ConnectedSpace Y]
    {f : X → Y} (_hf : IsHolomorphic f)
    (_hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) :
    BranchedCoverData X Y f := by
  sorry

end JacobianChallenge.Blueprint
