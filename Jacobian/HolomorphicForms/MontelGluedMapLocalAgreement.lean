import Jacobian.HolomorphicForms.GenusZeroUniformization
import Jacobian.HolomorphicForms.MontelLocalPatchRealization

/-!
# Glued-map local agreement on a realized Montel patch family

This file provides the **selector-free** local-formula step underneath the glued
forward map's smoothness (`…contMDiff_toMap`): on each source patch, the chosen
patch coordinate of `genusZeroGlobalGluing_toMap` agrees with that patch's own
coordinate.

The canonical forward candidate `genusZeroGlobalGluing_toMap` is defined for a
*bare* `GenusZeroGlobalPatchFamily` (it picks a patch via `Classical.choose` over
the cover and applies `targetChart.symm ∘ coord`) — it does **not** mention the
`GenusZeroNormalizedMontelPatchSelector`.  The existing agreement lemmas
(`genusZeroGlobalGluing_toMap_eq_uniformization`,
`genusZeroGlobalGluing_chart_expression_on_patch`) route through the selector,
which is the circular trap.  Here the agreement is proved instead from two honest
inputs — overlap compatibility (`hcompat`, exactly the conclusion shape of jc5's
`lem:montel-coherent-local-selector` overlap-agreement kernel) and the
per-patch target membership (`hmem`) — using only `OpenPartialHomeomorph.right_inv`.

The realization-consuming corollary then ties the glued map back to the
chart-ball Montel limit through a `MontelRealizedPatch`, discharging the consumer
obligation the realized-patch bundle was built to carry.

When jc1's existential patch-family provider lands it supplies `family` together
with the per-patch realizations, and jc5's overlap-agreement kernel supplies
`hcompat`; these lemmas then apply with zero changes.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/--
**Glued-map local agreement (selector-free).**

On each source patch `i`, applying that patch's target chart to the canonical
glued forward map recovers the patch's own coordinate:
`(family.patch i).targetChart (genusZeroGlobalGluing_toMap family x)
  = (family.patch i).coord x`.

Proved from overlap compatibility `hcompat` (which identifies the chosen patch's
target-chart inverse value with patch `i`'s) and per-patch target membership
`hmem` (so `OpenPartialHomeomorph.right_inv` applies).  No selector accessor, no
routing through `genusZeroGlobalGluing_toMap_eq_uniformization`.
-/
theorem genusZeroGlobalGluing_targetChart_toMap_eq_coord
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (family : GenusZeroGlobalPatchFamily X)
    (hcompat :
      ∀ i j x, x ∈ (family.patch i).source → x ∈ (family.patch j).source →
        (family.patch i).targetChart.symm ((family.patch i).coord x) =
          (family.patch j).targetChart.symm ((family.patch j).coord x))
    (hmem :
      ∀ i x, x ∈ (family.patch i).source →
        (family.patch i).coord x ∈ (family.patch i).targetChart.target)
    (i : family.PatchIndex) (x : X) (hx : x ∈ (family.patch i).source) :
    (family.patch i).targetChart (genusZeroGlobalGluing_toMap family x) =
      (family.patch i).coord x := by
  classical
  have hcover : x ∈ (family.patch (Classical.choose (family.patch_cover x))).source :=
    Classical.choose_spec (family.patch_cover x)
  have htoMap :
      genusZeroGlobalGluing_toMap family x =
        (family.patch (Classical.choose (family.patch_cover x))).targetChart.symm
          ((family.patch (Classical.choose (family.patch_cover x))).coord x) := rfl
  rw [htoMap, hcompat (Classical.choose (family.patch_cover x)) i x hcover hx]
  exact (family.patch i).targetChart.right_inv (hmem i x hx)

/--
**Glued-map local agreement, in chart-ball coordinates.**

The realization-consuming corollary: when source patch `i` is realized by a
`MontelRealizedPatch`, the glued forward map reads in the patch's target chart as
the chart-ball Montel limit evaluated in the realized source coordinate:
`(family.patch i).targetChart (genusZeroGlobalGluing_toMap family x)
  = localPatch.chartBall.toFun ((realized i).realization.sourceChart x)`.

This consumes `MontelRealizedPatch` (via the realization's `coord_eq_chartBall`),
tying the abstract glued-map value to the normalized Montel chart-ball data the
realized-patch bundle carries.
-/
theorem genusZeroGlobalGluing_targetChart_toMap_eq_chartBall
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (family : GenusZeroGlobalPatchFamily X)
    (localPatch : family.PatchIndex → GenusZeroLocalMontelChartPatch)
    (realized : ∀ i, MontelRealizedPatch X (localPatch i))
    (hpatch : ∀ i, (realized i).patch = family.patch i)
    (hcompat :
      ∀ i j x, x ∈ (family.patch i).source → x ∈ (family.patch j).source →
        (family.patch i).targetChart.symm ((family.patch i).coord x) =
          (family.patch j).targetChart.symm ((family.patch j).coord x))
    (hmem :
      ∀ i x, x ∈ (family.patch i).source →
        (family.patch i).coord x ∈ (family.patch i).targetChart.target)
    (i : family.PatchIndex) (x : X) (hx : x ∈ (family.patch i).source) :
    (family.patch i).targetChart (genusZeroGlobalGluing_toMap family x) =
      (localPatch i).chartBall.toFun ((realized i).realization.sourceChart x) := by
  rw [genusZeroGlobalGluing_targetChart_toMap_eq_coord family hcompat hmem i x hx,
    ← hpatch i]
  have hx' : x ∈ (realized i).patch.source := by rw [hpatch i]; exact hx
  exact (realized i).realization.coord_eq_chartBall x hx'

end JacobianChallenge.HolomorphicForms
