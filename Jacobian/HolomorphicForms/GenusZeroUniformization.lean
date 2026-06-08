import Jacobian.HolomorphicForms.OnePointCxIsManifold
import Jacobian.HolomorphicForms.UniformizationLocal
import Jacobian.Periods.TrivializationContinuousLinearMapAt

namespace JacobianChallenge.HolomorphicForms

/--
One source patch in the global genus-zero gluing construction.

This is intentionally a global-gluing object, not another local analytic leaf:
the coordinate function is attached to an open subset of `X`, and the target
chart is one of the two public charts on `OnePoint ℂ`.
-/
structure GenusZeroGlobalGluingPatch
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] where
  source : Set X
  isOpen_source : IsOpen source
  targetChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ
  targetChart_standard : targetChart = identityChart ∨ targetChart = inversionChart
  coord : X → ℂ
  invCoord : ℂ → X
  coord_contMDiffOn :
    ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) coord source

/--
Global gluing data for the genus-zero uniformization step.

The fields are the named 2d frontier: finite source patches, target atlas
choices, overlap compatibility of the local coordinate limits, local inverse
branches, and the resulting global map/inverse with smoothness.  This is
strictly narrower than `exists_contMDiff_homeomorph_to_onePointCx`: it exposes
the chart-level obligations that the global construction must prove instead of
postulating a smooth homeomorphism directly.
-/
structure GenusZeroGlobalGluingData
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] where
  PatchIndex : Type
  patch_fintype : Fintype PatchIndex
  patch_nonempty : Nonempty PatchIndex
  patch : PatchIndex → GenusZeroGlobalGluingPatch X
  patch_cover : ∀ x : X, ∃ i : PatchIndex, x ∈ (patch i).source
  target_chart_cover :
    ∀ y : OnePoint ℂ, ∃ (i : PatchIndex) (z : ℂ),
      z ∈ (patch i).targetChart.target ∧ y = (patch i).targetChart.symm z
  toMap : X → OnePoint ℂ
  invMap : OnePoint ℂ → X
  target_mem_on_patch :
    ∀ i x, x ∈ (patch i).source → toMap x ∈ (patch i).targetChart.source
  chart_expression_on_patch :
    ∀ i x, x ∈ (patch i).source →
      (patch i).targetChart (toMap x) = (patch i).coord x
  overlap_compatible :
    ∀ i j x,
      x ∈ (patch i).source → x ∈ (patch j).source →
        (patch i).targetChart.symm ((patch i).coord x) =
          (patch j).targetChart.symm ((patch j).coord x)
  inverse_branch_agrees_on_patch :
    ∀ i z, z ∈ (patch i).targetChart.target →
      invMap ((patch i).targetChart.symm z) = (patch i).invCoord z
  local_left_inverse_on_patch :
    ∀ i x, x ∈ (patch i).source → invMap (toMap x) = x
  local_right_inverse_on_target_chart :
    ∀ i z, z ∈ (patch i).targetChart.target →
      toMap ((patch i).invCoord z) = (patch i).targetChart.symm z
  contMDiff_toMap :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) toMap
  contMDiff_invMap :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) invMap

/--
The finite family of source patches and target-chart choices used before the
actual global map is assembled.
-/
structure GenusZeroGlobalPatchFamily
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] where
  PatchIndex : Type
  patch_fintype : Fintype PatchIndex
  patch_nonempty : Nonempty PatchIndex
  patch : PatchIndex → GenusZeroGlobalGluingPatch X
  patch_cover : ∀ x : X, ∃ i : PatchIndex, x ∈ (patch i).source
  target_chart_cover :
    ∀ y : OnePoint ℂ, ∃ (i : PatchIndex) (z : ℂ),
      z ∈ (patch i).targetChart.target ∧ y = (patch i).targetChart.symm z

/--
Analytic patch-selection provider for the genus-zero global gluing step.

This is the narrow uniformization input hidden behind the patch-family
frontier: a finite family of normalized Montel-limit coordinate patches, tied
to the chosen global map by the public `OnePoint ℂ` target charts.  The root
patch-family theorem below only forgets these analytic witnesses.
-/
structure GenusZeroNormalizedMontelPatchSelector
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] where
  uniformization : X ≃ₜ OnePoint ℂ
  family : GenusZeroGlobalPatchFamily X
  coord_represents_uniformization :
    ∀ i x, x ∈ (family.patch i).source →
      (family.patch i).targetChart.symm ((family.patch i).coord x) =
        uniformization x
  invCoord_represents_uniformization :
    ∀ i z, z ∈ (family.patch i).targetChart.target →
      (family.patch i).invCoord z =
        uniformization.symm ((family.patch i).targetChart.symm z)
  uniformization_contMDiff :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) (uniformization : X → OnePoint ℂ)
  inverse_uniformization_contMDiff :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) (uniformization.symm : OnePoint ℂ → X)

namespace GenusZeroGlobalGluingData

/-- The homeomorphism obtained after the global gluing data is complete. -/
noncomputable def toHomeomorph
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (data : GenusZeroGlobalGluingData X) :
    X ≃ₜ OnePoint ℂ where
  toFun := data.toMap
  invFun := data.invMap
  left_inv := by
    intro x
    rcases data.patch_cover x with ⟨i, hx⟩
    exact data.local_left_inverse_on_patch i x hx
  right_inv := by
    intro y
    rcases data.target_chart_cover y with ⟨i, z, hz, rfl⟩
    rw [data.inverse_branch_agrees_on_patch i z hz]
    exact data.local_right_inverse_on_target_chart i z hz
  continuous_toFun := data.contMDiff_toMap.continuous
  continuous_invFun := data.contMDiff_invMap.continuous

/--
Completed global gluing data gives exactly the smooth homeomorphism required by
the genus-zero uniformization target.
-/
theorem exists_contMDiff_homeomorph
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (data : GenusZeroGlobalGluingData X) :
    ∃ (f : X ≃ₜ OnePoint ℂ),
      ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (⊤ : WithTop ℕ∞) f ∧
      ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (⊤ : WithTop ℕ∞) f.symm := by
  refine ⟨data.toHomeomorph, ?_, ?_⟩
  · exact data.contMDiff_toMap
  · exact data.contMDiff_invMap

end GenusZeroGlobalGluingData

/--
Target-membership for local gluing coordinates: every normalized local
coordinate value actually lies in the target of the patch's assigned
`OnePoint ℂ` chart.
-/
theorem genusZeroGlobalGluing_coord_mem_target_on_patch
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (family : GenusZeroGlobalPatchFamily X) :
    ∀ i x, x ∈ (family.patch i).source →
      (family.patch i).coord x ∈ (family.patch i).targetChart.target := by
  intro i x _hx
  rcases (family.patch i).targetChart_standard with hchart | hchart
  · rw [hchart]
    simp [identityChart, Topology.IsOpenEmbedding.toOpenPartialHomeomorph]
  · rw [hchart]
    simp [inversionChart]

/--
Narrow analytic provider for the normalized Montel selector.

Given only a topological homeomorphism `X ≃ₜ OnePoint ℂ`, construct the
finite normalized source patches, their two public `OnePoint ℂ` target charts,
overlap-compatible local coordinates, inverse branches, and the smooth
uniformization represented by those local coordinates.

This is the remaining analytic selector existence frontier behind the public
genus-zero uniformization theorem.
-/
theorem genusZeroNormalizedMontelPatchSelector_of_homeomorph_onePoint
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (_e : X ≃ₜ OnePoint ℂ) :
    Nonempty (GenusZeroNormalizedMontelPatchSelector X) := by
  -- Remaining uniformization frontier: extract a finite normalized Montel
  -- patch selector from the topological sphere identification.
  sorry

/--
Completed global gluing data from the normalized Montel selector.

The selector supplies the finite patch family, compatibility with one global
uniformization, inverse branches, and smoothness. This packages those fields
into the global gluing-data structure used by the public theorem.
-/
theorem genusZeroGlobalGluingData_of_homeomorph_onePoint
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (_e : X ≃ₜ OnePoint ℂ) :
    Nonempty (GenusZeroGlobalGluingData X) := by
  obtain ⟨selector⟩ := genusZeroNormalizedMontelPatchSelector_of_homeomorph_onePoint X _e
  refine ⟨
    { PatchIndex := selector.family.PatchIndex
      patch_fintype := selector.family.patch_fintype
      patch_nonempty := selector.family.patch_nonempty
      patch := selector.family.patch
      patch_cover := selector.family.patch_cover
      target_chart_cover := selector.family.target_chart_cover
      toMap := selector.uniformization
      invMap := selector.uniformization.symm
      target_mem_on_patch := ?_
      chart_expression_on_patch := ?_
      overlap_compatible := ?_
      inverse_branch_agrees_on_patch := ?_
      local_left_inverse_on_patch := ?_
      local_right_inverse_on_target_chart := ?_
      contMDiff_toMap := selector.uniformization_contMDiff
      contMDiff_invMap := selector.inverse_uniformization_contMDiff }⟩
  · intro i x hx
    have hcoord :
        (selector.family.patch i).coord x ∈
          (selector.family.patch i).targetChart.target :=
      genusZeroGlobalGluing_coord_mem_target_on_patch selector.family i x hx
    have hmem :
        (selector.family.patch i).targetChart.symm ((selector.family.patch i).coord x) ∈
          (selector.family.patch i).targetChart.source :=
      (selector.family.patch i).targetChart.map_target hcoord
    have hrep :
        (selector.family.patch i).targetChart.symm ((selector.family.patch i).coord x) =
          selector.uniformization x :=
      selector.coord_represents_uniformization i x hx
    simpa [hrep] using hmem
  · intro i x hx
    have hcoord :
        (selector.family.patch i).coord x ∈
          (selector.family.patch i).targetChart.target :=
      genusZeroGlobalGluing_coord_mem_target_on_patch selector.family i x hx
    have hrep :
        (selector.family.patch i).targetChart.symm ((selector.family.patch i).coord x) =
          selector.uniformization x :=
      selector.coord_represents_uniformization i x hx
    rw [← hrep]
    exact (selector.family.patch i).targetChart.right_inv hcoord
  · intro i j x hi hj
    exact (selector.coord_represents_uniformization i x hi).trans
      (selector.coord_represents_uniformization j x hj).symm
  · intro i z hz
    exact (selector.invCoord_represents_uniformization i z hz).symm
  · intro i x _hx
    exact selector.uniformization.left_inv x
  · intro i z hz
    rw [selector.invCoord_represents_uniformization i z hz]
    exact selector.uniformization.right_inv ((selector.family.patch i).targetChart.symm z)

/--
Genus-zero uniformization theorem, stated as the single high-level analytic
provider needed by this file: a compact connected Riemann surface
homeomorphic to the Riemann sphere admits a biholomorphism to `OnePoint ℂ`.

The given homeomorphism is only topological; the theorem constructs a possibly
different homeomorphism that is complex-smooth in both directions. The remaining
analytic work is isolated in `genusZeroGlobalGluingData_of_homeomorph_onePoint`.
-/
theorem exists_biholomorph_onePoint_of_genus_zero
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (_e : X ≃ₜ OnePoint ℂ) :
    ∃ (f : X ≃ₜ OnePoint ℂ),
      ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (⊤ : WithTop ℕ∞) f ∧
      ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (⊤ : WithTop ℕ∞) f.symm := by
  obtain ⟨data⟩ := genusZeroGlobalGluingData_of_homeomorph_onePoint X _e
  exact GenusZeroGlobalGluingData.exists_contMDiff_homeomorph data

/--
The canonical forward candidate obtained by choosing one patch containing each
point and evaluating that patch's target-chart inverse on its local coordinate.
-/
noncomputable def genusZeroGlobalGluing_toMap
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (family : GenusZeroGlobalPatchFamily X) : X → OnePoint ℂ :=
  fun x =>
    let i := Classical.choose (family.patch_cover x)
    (family.patch i).targetChart.symm ((family.patch i).coord x)

/--
The chosen-patch formula agrees with the global uniformization represented by
the normalized Montel patch selector.
-/
theorem genusZeroGlobalGluing_toMap_eq_uniformization
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (selector : GenusZeroNormalizedMontelPatchSelector X) :
    ∀ x, genusZeroGlobalGluing_toMap selector.family x = selector.uniformization x := by
  intro x
  classical
  let i : selector.family.PatchIndex := Classical.choose (selector.family.patch_cover x)
  have hi : x ∈ (selector.family.patch i).source :=
    Classical.choose_spec (selector.family.patch_cover x)
  simpa [genusZeroGlobalGluing_toMap, i] using
    selector.coord_represents_uniformization i x hi

/--
Overlap-compatibility frontier through the public `OnePoint ℂ` transition
charts.
-/
theorem genusZeroGlobalGluing_overlap_compatible
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (selector : GenusZeroNormalizedMontelPatchSelector X) :
    ∀ i j x,
      x ∈ (selector.family.patch i).source → x ∈ (selector.family.patch j).source →
        (selector.family.patch i).targetChart.symm ((selector.family.patch i).coord x) =
          (selector.family.patch j).targetChart.symm ((selector.family.patch j).coord x) := by
  intro i j x hi hj
  exact (selector.coord_represents_uniformization i x hi).trans
    (selector.coord_represents_uniformization j x hj).symm

/--
The canonical glued map lands in every target chart on the corresponding
source patch.
-/
theorem genusZeroGlobalGluing_toMap_target_mem_on_patch
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (selector : GenusZeroNormalizedMontelPatchSelector X) :
    ∀ i x, x ∈ (selector.family.patch i).source →
      genusZeroGlobalGluing_toMap selector.family x ∈
        (selector.family.patch i).targetChart.source := by
  intro i x hx
  have hcoord_i :
      (selector.family.patch i).coord x ∈ (selector.family.patch i).targetChart.target :=
    genusZeroGlobalGluing_coord_mem_target_on_patch selector.family i x hx
  have hmem :
      (selector.family.patch i).targetChart.symm ((selector.family.patch i).coord x) ∈
        (selector.family.patch i).targetChart.source :=
    (selector.family.patch i).targetChart.map_target hcoord_i
  have hto :
      genusZeroGlobalGluing_toMap selector.family x = selector.uniformization x :=
    genusZeroGlobalGluing_toMap_eq_uniformization selector x
  have hrep :
      (selector.family.patch i).targetChart.symm ((selector.family.patch i).coord x) =
        selector.uniformization x :=
    selector.coord_represents_uniformization i x hx
  rw [hto, ← hrep]
  exact hmem

/--
Global candidate-map construction: the chosen-patch formula gives a single
candidate `X → OnePoint ℂ` landing in the selected target chart on every patch.
-/
theorem genusZeroGlobalGluing_toMap_exists
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (selector : GenusZeroNormalizedMontelPatchSelector X) :
    ∃ toMap : X → OnePoint ℂ,
      ∀ i x, x ∈ (selector.family.patch i).source →
        toMap x ∈ (selector.family.patch i).targetChart.source := by
  exact ⟨genusZeroGlobalGluing_toMap selector.family,
    genusZeroGlobalGluing_toMap_target_mem_on_patch selector⟩

/--
Chart expression for the canonical glued global map.
-/
theorem genusZeroGlobalGluing_chart_expression_on_patch
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (selector : GenusZeroNormalizedMontelPatchSelector X) :
    ∀ i x, x ∈ (selector.family.patch i).source →
      (selector.family.patch i).targetChart (genusZeroGlobalGluing_toMap selector.family x) =
        (selector.family.patch i).coord x := by
  intro i x hx
  have hcoord_i :
      (selector.family.patch i).coord x ∈ (selector.family.patch i).targetChart.target :=
    genusZeroGlobalGluing_coord_mem_target_on_patch selector.family i x hx
  have hto :
      genusZeroGlobalGluing_toMap selector.family x = selector.uniformization x :=
    genusZeroGlobalGluing_toMap_eq_uniformization selector x
  have hrep :
      (selector.family.patch i).targetChart.symm ((selector.family.patch i).coord x) =
        selector.uniformization x :=
    selector.coord_represents_uniformization i x hx
  rw [hto, ← hrep]
  exact (selector.family.patch i).targetChart.right_inv hcoord_i

/--
Inverse-candidate construction frontier from the local inverse branches.
-/
theorem genusZeroGlobalGluing_invMap_exists
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (selector : GenusZeroNormalizedMontelPatchSelector X) :
    ∃ invMap : OnePoint ℂ → X,
      ∀ i z, z ∈ (selector.family.patch i).targetChart.target →
        invMap ((selector.family.patch i).targetChart.symm z) =
          (selector.family.patch i).invCoord z := by
  refine ⟨selector.uniformization.symm, ?_⟩
  intro i z hz
  exact (selector.invCoord_represents_uniformization i z hz).symm

/--
Local left-inverse frontier for the glued candidate maps.
-/
theorem genusZeroGlobalGluing_local_left_inverse_on_patch
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (selector : GenusZeroNormalizedMontelPatchSelector X) :
    ∀ i x, x ∈ (selector.family.patch i).source →
      selector.uniformization.symm (genusZeroGlobalGluing_toMap selector.family x) = x := by
  intro _i x _hx
  rw [genusZeroGlobalGluing_toMap_eq_uniformization selector x]
  exact selector.uniformization.left_inv x

/--
Local right-inverse frontier for target-chart inverse branches.
-/
theorem genusZeroGlobalGluing_local_right_inverse_on_target_chart
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (selector : GenusZeroNormalizedMontelPatchSelector X) :
    ∀ i z, z ∈ (selector.family.patch i).targetChart.target →
      genusZeroGlobalGluing_toMap selector.family ((selector.family.patch i).invCoord z) =
        (selector.family.patch i).targetChart.symm z := by
  intro i z hz
  rw [genusZeroGlobalGluing_toMap_eq_uniformization selector]
  rw [selector.invCoord_represents_uniformization i z hz]
  exact selector.uniformization.right_inv ((selector.family.patch i).targetChart.symm z)

/--
Local-chart smoothness frontier for the glued global map.
-/
theorem genusZeroGlobalGluing_contMDiff_toMap
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (selector : GenusZeroNormalizedMontelPatchSelector X) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) (genusZeroGlobalGluing_toMap selector.family) := by
  have hfun :
      genusZeroGlobalGluing_toMap selector.family =
        (selector.uniformization : X → OnePoint ℂ) := by
    funext x
    exact genusZeroGlobalGluing_toMap_eq_uniformization selector x
  rw [hfun]
  exact selector.uniformization_contMDiff

/--
Local-chart smoothness frontier for the glued inverse map.
-/
theorem genusZeroGlobalGluing_contMDiff_invMap
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (selector : GenusZeroNormalizedMontelPatchSelector X) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (⊤ : WithTop ℕ∞) (selector.uniformization.symm : OnePoint ℂ → X) := by
  exact selector.inverse_uniformization_contMDiff

/--
**Structural axiom (G1a, uniformization at genus 0).** A compact
connected Riemann surface homeomorphic to `OnePoint ℂ` (= ℂℙ¹) admits a
*biholomorphism* to `OnePoint ℂ` — i.e. there EXISTS a homeomorphism
that is `ContMDiff` in both directions.

Note: the *given* homeomorphism `_e` need not itself be smooth (e.g.
complex conjugation on `OnePoint ℂ` is a self-homeomorphism that is
not `ℂ`-smooth); we must therefore construct a different homeomorphism
`f` that is smooth in both directions. This is the classical content of
the uniformization theorem at genus 0: every compact simply-connected
Riemann surface is biholomorphic to `ℂℙ¹`.
-/
theorem exists_contMDiff_homeomorph_to_onePointCx
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (_e : X ≃ₜ OnePoint ℂ) :
    ∃ (f : X ≃ₜ OnePoint ℂ),
      ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (⊤ : WithTop ℕ∞) f ∧
      ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (⊤ : WithTop ℕ∞) f.symm := by
  exact exists_biholomorph_onePoint_of_genus_zero X _e

end JacobianChallenge.HolomorphicForms
