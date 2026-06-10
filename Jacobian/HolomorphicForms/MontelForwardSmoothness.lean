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
charts' inverses are `ContMDiffOn` as manifold maps (proved here from Mathlib's
atlas API — `contMDiffOn_symm_of_mem_maximalAtlas`).  Composing gives the
per-patch `ContMDiffOn` of `u`.

The realization-consuming corollary reads the same smoothness through a
`MontelRealizedPatch`, so the chart-ball Montel data the realized-patch bundle
carries is the source coordinate.

Selector-free: nothing here touches `GenusZeroNormalizedMontelPatchSelector`.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/--
**Standard `OnePoint ℂ` target-chart inverse is smooth.**

Each of the two public target charts (`identityChart`, `inversionChart`) is an
atlas member of the `OnePoint ℂ` charted space, hence of the maximal atlas, so
its inverse is `ContMDiffOn` on the chart target by
`contMDiffOn_symm_of_mem_maximalAtlas`.
-/
theorem targetChart_symm_contMDiffOn
    (tc : OpenPartialHomeomorph (OnePoint ℂ) ℂ)
    (h : tc = identityChart ∨ tc = inversionChart) :
    ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) (tc.symm : ℂ → OnePoint ℂ) tc.target := by
  have hmem : tc ∈ atlas ℂ (OnePoint ℂ) := by
    show tc ∈ ({identityChart, inversionChart} : Set _)
    rcases h with h | h <;> simp [h]
  exact contMDiffOn_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (I := modelWithCornersSelf ℂ ℂ)
      (n := (⊤ : WithTop ℕ∞)) hmem)

/--
**Per-patch forward smoothness of the candidate uniformization.**

If a Montel patch family represents `u` in local public target charts
(`hcoord`) and each patch coordinate lands in its target-chart's target
(`hmem`), then `u` is `ContMDiffOn` on each patch source.

This is the local ingredient `genusZeroMontel_raw_global_patch_family_contMDiff_toMap`
consumes before the local-to-global assembly: `u =ᶠ targetChart.symm ∘ coord`
there, `coord` is `ContMDiffOn` (a patch field), and the target chart inverse is
`ContMDiffOn` by `targetChart_symm_contMDiffOn`.
-/
theorem montelForward_contMDiffOn_u_on_patch
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (family : GenusZeroGlobalPatchFamily X) (u : X → OnePoint ℂ)
    (hcoord :
      ∀ i x, x ∈ (family.patch i).source →
        (family.patch i).targetChart.symm ((family.patch i).coord x) = u x)
    (hmem :
      ∀ i x, x ∈ (family.patch i).source →
        (family.patch i).coord x ∈ (family.patch i).targetChart.target)
    (i : family.PatchIndex) :
    ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) u (family.patch i).source := by
  have hchart :
      ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (⊤ : WithTop ℕ∞) ((family.patch i).targetChart.symm : ℂ → OnePoint ℂ)
        (family.patch i).targetChart.target :=
    targetChart_symm_contMDiffOn (family.patch i).targetChart
      (family.patch i).targetChart_standard
  have hcomp :
      ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (⊤ : WithTop ℕ∞)
        ((family.patch i).targetChart.symm ∘ (family.patch i).coord)
        (family.patch i).source :=
    hchart.comp (family.patch i).coord_contMDiffOn (fun x hx => hmem i x hx)
  exact hcomp.congr (fun x hx => (hcoord i x hx).symm)

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
