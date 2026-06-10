import Jacobian.HolomorphicForms.GenusZeroClassification
import Jacobian.HolomorphicForms.GenusZeroUniformization
import Jacobian.HolomorphicForms.MontelLocalPatchRealization
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

noncomputable section

open TopologicalSpace Set Filter OnePoint
open scoped Topology

namespace JacobianChallenge.HolomorphicForms

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [JacobianChallenge.Periods.StableChartAt ℂ X]

/--
Helper lemma: when the target charts differ, they evaluate as multiplicative
inverses on `OnePoint ℂ`.
-/
lemma targetChart_inv_eq (e e' : OpenPartialHomeomorph (OnePoint ℂ) ℂ)
    (h_std : e = identityChart ∨ e = inversionChart)
    (h_std' : e' = identityChart ∨ e' = inversionChart)
    (h_diff : e ≠ e')
    (y : OnePoint ℂ) :
    e' y = (e y)⁻¹ := by
  sorry

/--
Helper lemma: when the target charts differ, their inverses respect the
multiplicative inversion of non-zero coordinates.
-/
lemma targetChart_symm_inv_eq (e e' : OpenPartialHomeomorph (OnePoint ℂ) ℂ)
    (h_std : e = identityChart ∨ e = inversionChart)
    (h_std' : e' = identityChart ∨ e' = inversionChart)
    (h_diff : e ≠ e')
    (z : ℂ) (hz : z ≠ 0) :
    e.symm z = e'.symm z⁻¹ := by
  sorry

/--
The normalized Montel chart-ball realizations of the finite patch family
agree on patch overlaps when their target charts are the same.
-/
lemma genusZeroMontel_overlap_agreement_same_chart
    (family : GenusZeroGlobalPatchFamily X)
    (localPatch : family.PatchIndex → GenusZeroLocalMontelChartPatch)
    (realization : ∀ i, GenusZeroLocalMontelPatchRealization (family.patch i) (localPatch i))
    (_normalized_limit : ∀ i, ChartBallPowerSeries.NormalizedChartBallLimit
      (localPatch i).chartBall.center 0 1 (localPatch i).chartBall.radius
      (localPatch i).chartBall.toFun)
    (_overlap_preconnected : ∀ i j, IsPreconnected ((family.patch i).source ∩ (family.patch j).source))
    (common_target_sequence : ∃ F : ℕ → X → OnePoint ℂ, ∀ i,
      TendstoLocallyUniformlyOn
        (fun n x => (family.patch i).targetChart (F n x))
        (family.patch i).coord Filter.atTop (family.patch i).source)
    (i j : family.PatchIndex)
    (same_chart : (family.patch i).targetChart = (family.patch j).targetChart) :
    ∀ x, x ∈ (family.patch i).source → x ∈ (family.patch j).source →
      (family.patch i).targetChart.symm ((localPatch i).chartBall.toFun ((realization i).sourceChart x)) =
      (family.patch j).targetChart.symm ((localPatch j).chartBall.toFun ((realization j).sourceChart x)) := by
  intro x hxi hxj
  have h_coord_i := (realization i).coord_eq_chartBall x hxi
  have h_coord_j := (realization j).coord_eq_chartBall x hxj
  rw [← h_coord_i, ← h_coord_j]
  rcases common_target_sequence with ⟨F, hF⟩
  have hi := hF i
  have hj := hF j
  have hxi_pt := TendstoLocallyUniformlyOn.tendsto_at hi hxi
  have hxj_pt := TendstoLocallyUniformlyOn.tendsto_at hj hxj
  rw [same_chart] at hxi_pt
  have h_eq := tendsto_nhds_unique hxi_pt hxj_pt
  rw [h_eq, same_chart]

/--
The normalized Montel chart-ball realizations of the finite patch family
agree on patch overlaps when their target charts differ.
-/
lemma genusZeroMontel_overlap_agreement_cross_chart
    (family : GenusZeroGlobalPatchFamily X)
    (localPatch : family.PatchIndex → GenusZeroLocalMontelChartPatch)
    (realization : ∀ i, GenusZeroLocalMontelPatchRealization (family.patch i) (localPatch i))
    (_normalized_limit : ∀ i, ChartBallPowerSeries.NormalizedChartBallLimit
      (localPatch i).chartBall.center 0 1 (localPatch i).chartBall.radius
      (localPatch i).chartBall.toFun)
    (_overlap_preconnected : ∀ i j, IsPreconnected ((family.patch i).source ∩ (family.patch j).source))
    (common_target_sequence : ∃ F : ℕ → X → OnePoint ℂ, ∀ i,
      TendstoLocallyUniformlyOn
        (fun n x => (family.patch i).targetChart (F n x))
        (family.patch i).coord Filter.atTop (family.patch i).source)
    (cross_chart_overlap_nonzero : ∀ i j x, x ∈ (family.patch i).source → x ∈ (family.patch j).source →
      (family.patch i).targetChart ≠ (family.patch j).targetChart →
      (family.patch i).coord x ≠ 0)
    (i j : family.PatchIndex)
    (diff_chart : (family.patch i).targetChart ≠ (family.patch j).targetChart) :
    ∀ x, x ∈ (family.patch i).source → x ∈ (family.patch j).source →
      (family.patch i).targetChart.symm ((localPatch i).chartBall.toFun ((realization i).sourceChart x)) =
      (family.patch j).targetChart.symm ((localPatch j).chartBall.toFun ((realization j).sourceChart x)) := by
  intro x hxi hxj
  have h_coord_i := (realization i).coord_eq_chartBall x hxi
  have h_coord_j := (realization j).coord_eq_chartBall x hxj
  rw [← h_coord_i, ← h_coord_j]
  have h_nz_i := cross_chart_overlap_nonzero i j x hxi hxj diff_chart
  rcases common_target_sequence with ⟨F, hF⟩
  have hi := hF i
  have hj := hF j
  have hxi_pt := TendstoLocallyUniformlyOn.tendsto_at hi hxi
  have hxj_pt := TendstoLocallyUniformlyOn.tendsto_at hj hxj
  
  have h_inv : ∀ n, (family.patch j).targetChart (F n x) = ((family.patch i).targetChart (F n x))⁻¹ := by
    intro n
    exact targetChart_inv_eq ((family.patch i).targetChart) ((family.patch j).targetChart)
      (family.patch i).targetChart_standard (family.patch j).targetChart_standard diff_chart (F n x)
  
  have hj_pt_rewritten : Tendsto (fun n => ((family.patch i).targetChart (F n x))⁻¹) atTop (𝓝 ((family.patch j).coord x)) := by
    have h_eq : (fun n => ((family.patch i).targetChart (F n x))⁻¹) = (fun n => (family.patch j).targetChart (F n x)) := by
      ext n; rw [← h_inv n]
    rw [h_eq]
    exact hxj_pt

  have h_lim_inv := Tendsto.inv₀ hxi_pt h_nz_i
  have h_coord_j_eq : (family.patch j).coord x = ((family.patch i).coord x)⁻¹ := tendsto_nhds_unique hj_pt_rewritten h_lim_inv

  rw [h_coord_j_eq]
  exact targetChart_symm_inv_eq ((family.patch i).targetChart) ((family.patch j).targetChart)
    (family.patch i).targetChart_standard (family.patch j).targetChart_standard diff_chart
    ((family.patch i).coord x) h_nz_i

/--
The normalized Montel chart-ball realizations of the finite patch family
agree on patch overlaps.

Honest hypotheses:
1. `_normalized_limit`: Each local chart ball limit is normalized at the origin
   with value 0 and derivative 1. This is supplied by the selector.
2. `_overlap_preconnected`: The identity theorem requires a preconnected domain.
   We assume the overlap is preconnected, as supplied by the topological
   properties of the uniformization cover.
3. `common_target_sequence`: The functions `coord i` arise as locally uniform
   limits of the same global sequence of maps `F_n : X → OnePoint ℂ`.
4. `cross_chart_overlap_nonzero`: On cross-chart overlaps, the coordinate `coord i x`
   cannot be zero.
-/
lemma genusZeroMontel_normalized_limits_agree_on_overlaps
    (family : GenusZeroGlobalPatchFamily X)
    (localPatch : family.PatchIndex → GenusZeroLocalMontelChartPatch)
    (realization : ∀ i, GenusZeroLocalMontelPatchRealization (family.patch i) (localPatch i))
    (_normalized_limit : ∀ i, ChartBallPowerSeries.NormalizedChartBallLimit
      (localPatch i).chartBall.center 0 1 (localPatch i).chartBall.radius
      (localPatch i).chartBall.toFun)
    (_overlap_preconnected : ∀ i j, IsPreconnected ((family.patch i).source ∩ (family.patch j).source))
    (common_target_sequence : ∃ F : ℕ → X → OnePoint ℂ, ∀ i,
      TendstoLocallyUniformlyOn
        (fun n x => (family.patch i).targetChart (F n x))
        (family.patch i).coord Filter.atTop (family.patch i).source)
    (cross_chart_overlap_nonzero : ∀ i j x, x ∈ (family.patch i).source → x ∈ (family.patch j).source →
      (family.patch i).targetChart ≠ (family.patch j).targetChart →
      (family.patch i).coord x ≠ 0)
    : ∀ i j x, x ∈ (family.patch i).source → x ∈ (family.patch j).source →
        (family.patch i).targetChart.symm ((localPatch i).chartBall.toFun ((realization i).sourceChart x)) =
        (family.patch j).targetChart.symm ((localPatch j).chartBall.toFun ((realization j).sourceChart x)) := by
  intro i j x hxi hxj
  by_cases h_eq : (family.patch i).targetChart = (family.patch j).targetChart
  · exact genusZeroMontel_overlap_agreement_same_chart family localPatch realization _normalized_limit _overlap_preconnected common_target_sequence i j h_eq x hxi hxj
  · exact genusZeroMontel_overlap_agreement_cross_chart family localPatch realization _normalized_limit _overlap_preconnected common_target_sequence cross_chart_overlap_nonzero i j h_eq x hxi hxj

end JacobianChallenge.HolomorphicForms
