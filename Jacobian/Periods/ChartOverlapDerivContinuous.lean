import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Complex.Basic

/-!
# Genuine chart-overlap derivative facts (no `StableChartAt`) — Milestone 0

This file is the foundation of the Path 1′ route (user-approved 2026-06-03):
eliminate the project's dependence on the FALSE `StableChartAt` locally-constant
-chart equality by supplying the genuine, C¹-manifold-true facts the downstream
consumers actually need.

## What is genuinely true (and proven here)

`mfderiv_chartAt_self_eq_id`: on any C¹ manifold, `mfderiv I I (chartAt H p₀) p₀
= id`. This is the chart-to-itself transition derivative; it needs NO
`StableChartAt`. Proven via `mfderiv_chartAt_eq_tangentCoordChange` +
`tangentCoordChange_self`.

## The remaining load-bearing fact (Milestone 0 continuity — see note below)

The 6 root consumers also need **operator-norm continuity at `p₀`** of
`b ↦ mfderiv (chartAt H p₀) b = tangentCoordChange I b p₀ b`. This is TRUE but is
NOT a one-line consequence of Mathlib's primitives: every Mathlib continuity
lemma for the chart-overlap derivative
(`VectorBundleCore.continuousOn_coordChange i j`,
`continuousOn_tangentCoordChange x y`, `VectorBundle.continuousOn_coordChange e e'`)
fixes BOTH chart indices, whereas this object has its *source* index `achart b`
VARYING with the evaluation point `b` (because `chartAt b` moves as `b` moves).
This is exactly the obstruction `StableChartAt` was introduced to dodge.

The honest continuity is provable by building moving-base-chart infrastructure
on top of `contDiffOn_fderiv_coord_change` (the chart-transition derivative
`fderivWithin (extChartAt p₀ ∘ (extChartAt b).symm)` is continuous as `b`
varies), but that is a dedicated multi-lemma effort, tracked as the remaining
Milestone-0 work. See `.sci/result.md` for the feasibility verdict and scope.

No `axiom`, no fake instance; `Challenge.lean` is untouched.
-/

namespace JacobianChallenge.Periods

open Bundle Set Filter
open scoped Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (1 : WithTop ℕ∞) M]

/-- **Value at the basepoint (genuine, no `StableChartAt`):**
`mfderiv I I (chartAt H p₀) p₀ = id`. The chart-transition derivative from a
chart to itself, evaluated at the centre, is the identity. -/
theorem mfderiv_chartAt_self_eq_id (p₀ : M) :
    mfderiv I I (chartAt H p₀) p₀ = ContinuousLinearMap.id 𝕜 E := by
  have hmem : p₀ ∈ (chartAt H p₀).source := mem_chart_source H p₀
  rw [mfderiv_chartAt_eq_tangentCoordChange (I := I) (M := M) (y := p₀) (x := p₀) hmem]
  ext v
  apply tangentCoordChange_self (I := I) (x := p₀) (z := p₀) (v := v)
  rw [extChartAt_source]
  exact hmem

end JacobianChallenge.Periods
