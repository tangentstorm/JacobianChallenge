import Jacobian.HolomorphicForms.GenusZeroUniformization
import Jacobian.HolomorphicForms.OnePointCxIsManifold

/-!
# Per-patch inverse smoothness of the candidate uniformization

This file provides the **per-patch smoothness reading for the inverse map**
`u.symm : OnePoint ℂ → X` — the mirror of `MontelForwardSmoothness`, and the
last local ingredient underneath the inverse-smoothness leaf
`genusZeroMontel_raw_global_patch_family_contMDiff_invMap` before the
local-to-global gluing argument.

On each target-chart source region, `u.symm` agrees with `invCoord ∘ targetChart`
(the family's inverse-branch hypothesis `hinv`, rewritten through
`targetChart.left_inv`).  The standard `OnePoint ℂ` target charts are atlas
members, so the forward chart map is `ContMDiffOn` on its source (Mathlib's
`contMDiffOn_of_mem_maximalAtlas`); the inverse branch's smoothness on
`targetChart.target` is supplied as an honest hypothesis-as-input
(`invCoord` smoothness is **not** a `GenusZeroGlobalGluingPatch` field, unlike
the forward `coord_contMDiffOn`).  Composing gives the per-patch `ContMDiffOn` of
`u.symm`.

Selector-free: nothing here touches `GenusZeroNormalizedMontelPatchSelector`.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/--
**Standard `OnePoint ℂ` target chart is smooth.**

The forward direction mirror of `targetChart_symm_contMDiffOn`: each of the two
public target charts (`identityChart`, `inversionChart`) is an atlas member of
the `OnePoint ℂ` charted space, hence of the maximal atlas, so the chart map
itself is `ContMDiffOn` on the chart source by `contMDiffOn_of_mem_maximalAtlas`.
-/
theorem targetChart_contMDiffOn
    (tc : OpenPartialHomeomorph (OnePoint ℂ) ℂ)
    (h : tc = identityChart ∨ tc = inversionChart) :
    ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) (tc : OnePoint ℂ → ℂ) tc.source := by
  have hmem : tc ∈ atlas ℂ (OnePoint ℂ) := by
    show tc ∈ ({identityChart, inversionChart} : Set _)
    rcases h with h | h <;> simp [h]
  exact contMDiffOn_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (I := modelWithCornersSelf ℂ ℂ)
      (n := (⊤ : WithTop ℕ∞)) hmem)

/--
**Per-patch inverse smoothness of the candidate uniformization.**

If a Montel patch family represents the inverse branches of a candidate
`u : X ≃ₜ OnePoint ℂ` in local public target charts (`hinv`) and each inverse
branch is `ContMDiffOn` on its target-chart target (`hinv_smooth`, an honest
input), then `u.symm` is `ContMDiffOn` on each patch's target-chart source.

This is the local ingredient
`genusZeroMontel_raw_global_patch_family_contMDiff_invMap` consumes before the
local-to-global assembly: on `targetChart.source`, `u.symm = invCoord ∘ targetChart`
(from `hinv` at `z = targetChart y`, via `targetChart.left_inv`); the forward
chart is `ContMDiffOn` by `targetChart_contMDiffOn` and the inverse branch by
`hinv_smooth`.
-/
theorem montelInverse_contMDiffOn_uSymm_on_patch
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (u : X ≃ₜ OnePoint ℂ) (family : GenusZeroGlobalPatchFamily X)
    (hinv :
      ∀ i z, z ∈ (family.patch i).targetChart.target →
        (family.patch i).invCoord z =
          u.symm ((family.patch i).targetChart.symm z))
    (hinv_smooth :
      ∀ i,
        ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
          (⊤ : WithTop ℕ∞) (family.patch i).invCoord
          (family.patch i).targetChart.target)
    (i : family.PatchIndex) :
    ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) (u.symm : OnePoint ℂ → X) (family.patch i).targetChart.source := by
  have hchart :
      ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (⊤ : WithTop ℕ∞) ((family.patch i).targetChart : OnePoint ℂ → ℂ)
        (family.patch i).targetChart.source :=
    targetChart_contMDiffOn (family.patch i).targetChart
      (family.patch i).targetChart_standard
  have hsub :
      (family.patch i).targetChart.source ⊆
        (family.patch i).targetChart ⁻¹' (family.patch i).targetChart.target :=
    fun y hy => (family.patch i).targetChart.map_source hy
  have hcomp :
      ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (⊤ : WithTop ℕ∞)
        ((family.patch i).invCoord ∘ (family.patch i).targetChart)
        (family.patch i).targetChart.source :=
    (hinv_smooth i).comp hchart hsub
  refine hcomp.congr (fun y hy => ?_)
  have hz : (family.patch i).targetChart y ∈ (family.patch i).targetChart.target :=
    (family.patch i).targetChart.map_source hy
  rw [Function.comp_apply, hinv i ((family.patch i).targetChart y) hz,
    (family.patch i).targetChart.left_inv hy]

end JacobianChallenge.HolomorphicForms
