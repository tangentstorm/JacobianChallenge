import Jacobian.HolomorphicForms.GenusZeroClassification
import Jacobian.HolomorphicForms.GenusZeroUniformization
import Jacobian.HolomorphicForms.MontelLocalPatchRealization
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

noncomputable section

open TopologicalSpace Set

namespace JacobianChallenge.HolomorphicForms

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [JacobianChallenge.Periods.StableChartAt ℂ X]

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
agree on patch overlaps.

Honest hypotheses:
1. `normalized_limit`: Each local chart ball limit is normalized at the origin
   with value 0 and derivative 1. This is supplied by the selector.
2. `overlap_connected`: The identity theorem requires a preconnected domain.
   We assume the overlap is preconnected, as supplied by the topological
   properties of the uniformization cover.
3. `common_target_sequence`: The functions `coord i` arise as locally uniform
   limits of the same global sequence of maps `F_n : X → OnePoint ℂ`.
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
    : ∀ i j x, x ∈ (family.patch i).source → x ∈ (family.patch j).source →
        (family.patch i).targetChart.symm ((localPatch i).chartBall.toFun ((realization i).sourceChart x)) =
        (family.patch j).targetChart.symm ((localPatch j).chartBall.toFun ((realization j).sourceChart x)) := by
  sorry

end JacobianChallenge.HolomorphicForms
