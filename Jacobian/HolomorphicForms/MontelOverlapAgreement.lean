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

lemma identityChart_source_eq : (identityChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ).source = range ((↑) : ℂ → OnePoint ℂ) := by
  simp [identityChart, Topology.IsOpenEmbedding.toOpenPartialHomeomorph]

lemma inversionChart_source_eq : (inversionChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ).source = {↑(0 : ℂ)}ᶜ := rfl

lemma identityChart_apply_coe (z : ℂ) : (identityChart : OnePoint ℂ → ℂ) ↑z = z :=
  OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph_left_inv

lemma eventual_mem_source (e e' : OpenPartialHomeomorph (OnePoint ℂ) ℂ)
    (h_std : e = identityChart ∨ e = inversionChart)
    (h_std' : e' = identityChart ∨ e' = inversionChart)
    (h_diff : e ≠ e')
    (F : ℕ → OnePoint ℂ) (z z' : ℂ) (hz : z ≠ 0) (hz' : z' ≠ 0)
    (h_lim : Tendsto (fun n => e (F n)) atTop (𝓝 z))
    (h_lim' : Tendsto (fun n => e' (F n)) atTop (𝓝 z')) :
    ∀ᶠ n in atTop, F n ∈ e.source ∩ e'.source := by
  have h_id_0 : (identityChart : OnePoint ℂ → ℂ) ↑(0:ℂ) = 0 := identityChart_apply_coe 0
  have h_inv_infty : (inversionChart : OnePoint ℂ → ℂ) ∞ = 0 := rfl
  have h_ev : ∀ᶠ n in atTop, e (F n) ≠ 0 :=
    Tendsto.eventually_ne h_lim hz
  have h_ev' : ∀ᶠ n in atTop, e' (F n) ≠ 0 :=
    Tendsto.eventually_ne h_lim' hz'
  filter_upwards [h_ev, h_ev'] with n hn hn'
  rcases h_std with rfl | rfl
  · rcases h_std' with rfl | rfl
    · contradiction
    · constructor
      · rw [identityChart_source_eq]
        have : F n ≠ ∞ := by
          intro h; rw [h] at hn'; exact hn' h_inv_infty
        cases h : F n with
        | infty => exact (this h).elim
        | coe w => exact ⟨w, rfl⟩
      · rw [inversionChart_source_eq]
        have : F n ≠ ↑(0:ℂ) := by
          intro h; rw [h] at hn; exact hn h_id_0
        exact this
  · rcases h_std' with rfl | rfl
    · constructor
      · rw [inversionChart_source_eq]
        have : F n ≠ ↑(0:ℂ) := by
          intro h; rw [h] at hn'; exact hn' h_id_0
        exact this
      · rw [identityChart_source_eq]
        have : F n ≠ ∞ := by
          intro h; rw [h] at hn; exact hn h_inv_infty
        cases h : F n with
        | infty => exact (this h).elim
        | coe w => exact ⟨w, rfl⟩
    · contradiction

/--
Helper lemma: when the target charts differ, they evaluate as multiplicative
inverses on their common honest domain in `OnePoint ℂ`.
-/
lemma targetChart_inv_eq (e e' : OpenPartialHomeomorph (OnePoint ℂ) ℂ)
    (h_std : e = identityChart ∨ e = inversionChart)
    (h_std' : e' = identityChart ∨ e' = inversionChart)
    (h_diff : e ≠ e')
    (y : OnePoint ℂ)
    (hy : y ∈ e.source)
    (hy' : y ∈ e'.source) :
    e' y = (e y)⁻¹ := by
  rcases h_std with rfl | rfl
  · rcases h_std' with rfl | rfl
    · contradiction
    · have hy_id : y ∈ identityChart.source := hy
      have hy_inv : y ∈ inversionChart.source := hy'
      rw [identityChart_source_eq] at hy_id
      obtain ⟨z, hz_eq⟩ := hy_id
      subst hz_eq
      have hz_ne_zero : z ≠ 0 := by
        intro h
        subst h
        rw [inversionChart_source_eq] at hy_inv
        exact hy_inv rfl
      have h1 : (identityChart : OnePoint ℂ → ℂ) ↑z = z := identityChart_apply_coe z
      have h2 : (inversionChart : OnePoint ℂ → ℂ) ↑z = z⁻¹ := rfl
      rw [h1, h2]
  · rcases h_std' with rfl | rfl
    · have hy_inv : y ∈ inversionChart.source := hy
      have hy_id : y ∈ identityChart.source := hy'
      rw [identityChart_source_eq] at hy_id
      obtain ⟨z, hz_eq⟩ := hy_id
      subst hz_eq
      have hz_ne_zero : z ≠ 0 := by
        intro h
        subst h
        rw [inversionChart_source_eq] at hy_inv
        exact hy_inv rfl
      have h1 : (identityChart : OnePoint ℂ → ℂ) ↑z = z := identityChart_apply_coe z
      have h2 : (inversionChart : OnePoint ℂ → ℂ) ↑z = z⁻¹ := rfl
      rw [h1, h2, inv_inv]
    · contradiction

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
  rcases h_std with rfl | rfl
  · rcases h_std' with rfl | rfl
    · contradiction
    · change ↑z = invBwd z⁻¹
      have : z⁻¹ ≠ 0 := inv_ne_zero hz
      rw [invBwd_ne_zero this, inv_inv]
  · rcases h_std' with rfl | rfl
    · change invBwd z = ↑(z⁻¹)
      rw [invBwd_ne_zero hz]
    · contradiction

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
  
  have h_nz_j := cross_chart_overlap_nonzero j i x hxj hxi diff_chart.symm
  have h_ev_mem := eventual_mem_source ((family.patch i).targetChart) ((family.patch j).targetChart)
    (family.patch i).targetChart_standard (family.patch j).targetChart_standard diff_chart
    (fun n => F n x) ((family.patch i).coord x) ((family.patch j).coord x) h_nz_i h_nz_j
    hxi_pt hxj_pt

  have hj_pt_rewritten : Tendsto (fun n => ((family.patch i).targetChart (F n x))⁻¹) atTop (𝓝 ((family.patch j).coord x)) := by
    have h_eq_ev : ∀ᶠ n in atTop, ((family.patch i).targetChart (F n x))⁻¹ = (family.patch j).targetChart (F n x) := by
      filter_upwards [h_ev_mem] with n hn
      have h_inv_eq := targetChart_inv_eq ((family.patch i).targetChart) ((family.patch j).targetChart)
        (family.patch i).targetChart_standard (family.patch j).targetChart_standard diff_chart (F n x) hn.1 hn.2
      rw [h_inv_eq]
    exact (tendsto_congr' h_eq_ev).mpr hxj_pt

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
