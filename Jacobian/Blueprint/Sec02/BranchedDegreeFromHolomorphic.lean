import Jacobian.Blueprint.Sec02.WeightedFiberCardConst

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

The remaining obstacle — well-definedness of the branched degree
(`fiberSum_const`, formerly named `weightedFiberCard_const`) — has been
split into four sub-leaves in `Sec02/WeightedFiberCardConst.lean`:

  * leaf A — `mapAnalyticOrderAt_ramified_finite` (branch locus
    finite),
  * leaf B — `IsHolomorphicAt.exists_local_inj_of_unramified` (local
    injectivity at unramified points),
  * leaf C — `IsHolomorphicAt.exists_local_kfold_of_ramified` (local
    `k`-fold structure at ramified points),
  * leaf D — `isHolomorphic_weightedFiberSum_isLocallyConstant`
    (local conservation of weighted fibre count).

The final-assembly theorem `isHolomorphic_weightedFiberSum_const`
(in that file) combines leaf D with `PreconnectedSpace Y` and is
sorry-free.  Its statement is exactly the field needed for
`weightedFiberCard_const` here, so this constructor body is also
sorry-free *modulo* the four sub-leaves (each still `sorry`). -/

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
from `isHolomorphic_finite_fiber`; constancy of the fibre sum comes
from `isHolomorphic_weightedFiberSum_const`. -/
noncomputable def branchedCoverData_of_nonconstant_holomorphic
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    [CompactSpace X] [T2Space X]
    [PreconnectedSpace X] [T2Space Y] [PreconnectedSpace Y]
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
    {f : X → Y} (hf : IsHolomorphic f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) :
    BranchedCoverData X Y f where
  ramificationIndex := mapAnalyticOrderAt f
  ramificationIndex_pos := mapAnalyticOrderAt_pos hf hnonconst
  finite_fiber := isHolomorphic_finite_fiber hf hnonconst
  fiberSum_const := isHolomorphic_weightedFiberSum_const hf hnonconst

end JacobianChallenge.Blueprint
