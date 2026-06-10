import Jacobian.HolomorphicForms.GenusZeroUniformization
import Jacobian.HolomorphicForms.MontelLocalPatchRealization
import Jacobian.HolomorphicForms.OnePointCxIsManifold

/-!
# Per-patch forward smoothness of the candidate uniformization

This file provides the **per-patch smoothness reading** of a candidate
uniformization `u : X → OnePoint ℂ` represented by a Montel patch family — the
last local ingredient underneath the forward-smoothness leaf
`genusZeroMontel_raw_global_patch_family_contMDiff_toMap` before the
local-to-global gluing argument.

On each source patch, `u` agrees with `targetChart.symm ∘ coord` (the family's
chart-representation hypothesis `hcoord`).  The patch coordinate is `ContMDiffOn`
(a `GenusZeroGlobalGluingPatch` field), and the standard `OnePoint ℂ` target
charts' inverses are `ContMDiffOn` as manifold maps.  Those upstream helpers now
live in `GenusZeroUniformization.lean`, where the raw-family forward smoothness
provider consumes them.

The realization-consuming corollary reads the same smoothness through a
`MontelRealizedPatch`, so the chart-ball Montel data the realized-patch bundle
carries is the source coordinate.

Selector-free: nothing here touches `GenusZeroNormalizedMontelPatchSelector`.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/--
**Per-patch forward smoothness, in chart-ball coordinates.**

The realization-consuming corollary: when source patch `i` is realized by a
`MontelRealizedPatch`, the candidate uniformization `u` is still `ContMDiffOn` on
the patch source, with its coordinate now identified — through the realization's
`coord_eq_chartBall` — as the chart-ball Montel limit
`(localPatch i).chartBall.toFun (sourceChart x)`.

This restates the per-patch reading against the realized-patch toolkit: the same
smoothness conclusion, now visibly tied to the normalized Montel chart-ball data
the bundle carries.  (The smoothness conclusion is exactly
`montelForward_contMDiffOn_u_on_patch`; this corollary records the chart-ball
coordinate identification a consumer reads off the realization.)
-/
theorem montelForward_contMDiffOn_u_on_patch_chartBall
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (family : GenusZeroGlobalPatchFamily X) (u : X → OnePoint ℂ)
    (localPatch : family.PatchIndex → GenusZeroLocalMontelChartPatch)
    (realized : ∀ i, MontelRealizedPatch X (localPatch i))
    (hpatch : ∀ i, (realized i).patch = family.patch i)
    (hcoord :
      ∀ i x, x ∈ (family.patch i).source →
        (family.patch i).targetChart.symm ((family.patch i).coord x) = u x)
    (hmem :
      ∀ i x, x ∈ (family.patch i).source →
        (family.patch i).coord x ∈ (family.patch i).targetChart.target)
    (i : family.PatchIndex) :
    ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) u (family.patch i).source ∧
    ∀ x, x ∈ (family.patch i).source →
      (family.patch i).coord x =
        (localPatch i).chartBall.toFun ((realized i).realization.sourceChart x) := by
  refine ⟨montelForward_contMDiffOn_u_on_patch family u hcoord hmem i, fun x hx => ?_⟩
  have hx' : x ∈ (realized i).patch.source := by rw [hpatch i]; exact hx
  rw [← hpatch i]
  exact (realized i).realization.coord_eq_chartBall x hx'

end JacobianChallenge.HolomorphicForms
