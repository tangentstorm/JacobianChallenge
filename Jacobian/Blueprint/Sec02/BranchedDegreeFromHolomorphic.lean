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

Three of the four originally-named obstacles have been discharged in
`Jacobian/HolomorphicForms/HolomorphicMap.lean`:

  1. **Chart-independence of `mapAnalyticOrderAt`** — sorry-free,
     `analyticOrderAt_alternate_chart_eq` /
     `mapAnalyticOrderAt_eq_of_mem_maximalAtlas`.
  2. **Positivity of `mapAnalyticOrderAt`** for nonconstant
     holomorphic maps on a preconnected source — sorry-free,
     `mapAnalyticOrderAt_pos`.
  3. **Finite fibres** via the chart-local identity principle and
     Bolzano–Weierstrass — sorry-free, `isHolomorphic_finite_fiber`.

The remaining obstacle is the genuinely hard one:

  4. **Constancy of the weighted fibre count
     (`weightedFiberCard_const`)** — the well-definedness of the
     branched degree.  Standard proofs use local triviality of
     branched coverings off the (finite) branch locus plus a
     continuity argument across branch values, or homological /
     proper-degree machinery.  The single remaining `sorry` in this
     file is precisely that step. -/

namespace JacobianChallenge.Blueprint

open JacobianChallenge.HolomorphicForms.HolomorphicMap
open scoped Manifold ContDiff

/-- **Plan leaf 8.** Analytic constructor for `BranchedCoverData`: a
holomorphic, non-locally-constant map `f : X → Y` between two complex
1-manifolds (compact Hausdorff preconnected source, `T2` connected
target) packages as a branched-cover datum, with the chart-local
analytic order `mapAnalyticOrderAt f` realising the ramification
index.

Three of the four structural obligations are discharged: the
ramification index and its positivity come from
`mapAnalyticOrderAt` and `mapAnalyticOrderAt_pos`; finite fibres come
from `isHolomorphic_finite_fiber`; the default `weightedFiberCard`
field is the explicit fibre sum, so `weightedFiberCard_eq` is `rfl`.
The remaining `sorry` is `weightedFiberCard_const` — the
well-definedness of the branched degree. -/
noncomputable def branchedCoverData_of_nonconstant_holomorphic
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    [CompactSpace X] [T2Space X]
    [PreconnectedSpace X] [T2Space Y]
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
    {f : X → Y} (hf : IsHolomorphic f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) :
    BranchedCoverData X Y f where
  ramificationIndex := mapAnalyticOrderAt f
  ramificationIndex_pos := mapAnalyticOrderAt_pos hf hnonconst
  finite_fiber := isHolomorphic_finite_fiber hf hnonconst
  weightedFiberCard_eq := fun _ => rfl
  weightedFiberCard_const := by
    -- The single remaining analytic obstacle: the weighted fibre count
    -- is constant on `Y`.  This is the well-definedness of the branched
    -- degree.  Standard proofs use:
    --   * branch locus discreteness + finiteness (compactness),
    --   * local triviality of the branched cover off the finite set of
    --     branch values,
    --   * continuity across branch values (the weighted count "absorbs"
    --     ramification mass at branch values to compensate for fibres
    --     converging together).
    -- This step is genuinely hard and is the single biggest remaining
    -- gap in the branched-degree story.
    sorry

end JacobianChallenge.Blueprint
