import Jacobian.HolomorphicForms.GenusZeroClassification
import Jacobian.HolomorphicForms.GenusZeroUniformization
import Jacobian.HolomorphicForms.MontelLocalPatchRealization

noncomputable section

open TopologicalSpace Set

namespace JacobianChallenge.HolomorphicForms

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
  [JacobianChallenge.Periods.StableChartAt ℂ X]

/--
The normalized Montel chart-ball realizations of the finite patch family
agree on patch overlaps.

Honest hypotheses:
1. `normalized_limit`: Each local chart ball limit is normalized at the origin
   with value 0 and derivative 1. This is supplied by the selector.
2. `overlap_connected`: The identity theorem requires a preconnected domain.
   We assume the overlap is preconnected, as supplied by the topological
   properties of the uniformization cover.
-/
lemma genusZeroMontel_normalized_limits_agree_on_overlaps
    (family : GenusZeroGlobalPatchFamily X)
    (localPatch : family.PatchIndex → GenusZeroLocalMontelChartPatch)
    (realization : ∀ i, GenusZeroLocalMontelPatchRealization (family.patch i) (localPatch i))
    (normalized_limit : ∀ i, ChartBallPowerSeries.NormalizedChartBallLimit
      (localPatch i).chartBall.center 0 1 (localPatch i).chartBall.radius
      (localPatch i).chartBall.toFun)
    (overlap_preconnected : ∀ i j, IsPreconnected ((family.patch i).source ∩ (family.patch j).source))
    (overlap_nonempty : ∀ i j, ((family.patch i).source ∩ (family.patch j).source).Nonempty)
    : ∀ i j x, x ∈ (family.patch i).source → x ∈ (family.patch j).source →
        (family.patch i).targetChart.symm ((localPatch i).chartBall.toFun ((realization i).sourceChart x)) =
        (family.patch j).targetChart.symm ((localPatch j).chartBall.toFun ((realization j).sourceChart x)) := by
  sorry

end JacobianChallenge.HolomorphicForms
