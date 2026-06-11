import Jacobian.HolomorphicForms.StageFrontierChartCover

/-!
# Model stage sequence on `OnePoint ℂ`

This module records the A2 model-stage sequence used before selected-compact
containment and bordered-stage assembly.  The stages are open annuli in the two
standard charts on `OnePoint ℂ`, then pulled back along the fixed topological
homeomorphism to an arbitrary genus-zero surface.
-/

namespace JacobianChallenge.HolomorphicForms

open Set
open scoped Topology

noncomputable section

/-- The radius used for the `n`th model stage in both standard charts. -/
def onePointModelStageRadius (n : ℕ) : ℝ :=
  (n : ℝ) + 2

/--
The `n`th model stage on `OnePoint ℂ`: points lying in both standard chart
sources whose identity and inversion chart coordinates have norm bounded by
`n + 2`.
-/
def onePointModelStage (n : ℕ) : Set (OnePoint ℂ) :=
  (identityChart.source ∩
      identityChart ⁻¹' Metric.ball (0 : ℂ) (onePointModelStageRadius n)) ∩
    (inversionChart.source ∩
      inversionChart ⁻¹' Metric.ball (0 : ℂ) (onePointModelStageRadius n))

private theorem onePointModelStageRadius_mono {m n : ℕ} (hmn : m ≤ n) :
    onePointModelStageRadius m ≤ onePointModelStageRadius n := by
  unfold onePointModelStageRadius
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_right (Nat.cast_le.mpr hmn : (m : ℝ) ≤ n) (2 : ℝ)

/-- Each model stage is open in `OnePoint ℂ`. -/
theorem isOpen_onePointModelStage (n : ℕ) :
    IsOpen (onePointModelStage n) := by
  unfold onePointModelStage
  exact
    (identityChart.isOpen_inter_preimage Metric.isOpen_ball).inter
      (inversionChart.isOpen_inter_preimage Metric.isOpen_ball)

/-- The model stages are monotone increasing. -/
theorem monotone_onePointModelStage {m n : ℕ} (hmn : m ≤ n) :
    onePointModelStage m ⊆ onePointModelStage n := by
  intro x hx
  exact
    ⟨⟨hx.1.1,
        Metric.ball_subset_ball (onePointModelStageRadius_mono hmn) hx.1.2⟩,
      ⟨hx.2.1,
        Metric.ball_subset_ball (onePointModelStageRadius_mono hmn) hx.2.2⟩⟩

/-- Model stages lie in the identity chart source. -/
theorem onePointModelStage_subset_identityChart_source (n : ℕ) :
    onePointModelStage n ⊆ identityChart.source := by
  intro x hx
  exact hx.1.1

/-- Model stages lie in the inversion chart source. -/
theorem onePointModelStage_subset_inversionChart_source (n : ℕ) :
    onePointModelStage n ⊆ inversionChart.source := by
  intro x hx
  exact hx.2.1

/-- Model stages lie in the intersection of the two standard chart sources. -/
theorem onePointModelStage_subset_standardChart_sources (n : ℕ) :
    onePointModelStage n ⊆ identityChart.source ∩ inversionChart.source := by
  intro x hx
  exact ⟨hx.1.1, hx.2.1⟩

/-- Pull the model stages back along a topological genus-zero identification. -/
def pulledBackModelStage
    {X : Type*} [TopologicalSpace X] (e : X ≃ₜ OnePoint ℂ) (n : ℕ) : Set X :=
  e ⁻¹' onePointModelStage n

/-- Pulled-back model stages are open. -/
theorem isOpen_pulledBackModelStage
    {X : Type*} [TopologicalSpace X] (e : X ≃ₜ OnePoint ℂ) (n : ℕ) :
    IsOpen (pulledBackModelStage e n) := by
  unfold pulledBackModelStage
  exact e.continuous.isOpen_preimage _ (isOpen_onePointModelStage n)

/-- Pulled-back model stages are monotone increasing. -/
theorem monotone_pulledBackModelStage
    {X : Type*} [TopologicalSpace X] (e : X ≃ₜ OnePoint ℂ)
    {m n : ℕ} (hmn : m ≤ n) :
    pulledBackModelStage e m ⊆ pulledBackModelStage e n := by
  exact preimage_mono (monotone_onePointModelStage hmn)

private theorem exists_nat_for_modelStageRadius_ge (r₁ r₂ : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      r₁ ≤ onePointModelStageRadius n ∧ r₂ ≤ onePointModelStageRadius n := by
  obtain ⟨N, hN⟩ := exists_nat_ge (max r₁ r₂)
  refine ⟨N, ?_⟩
  intro n hn
  have hNn : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
  have hmaxn : max r₁ r₂ ≤ (n : ℝ) := hN.trans hNn
  have hnrad : (n : ℝ) ≤ onePointModelStageRadius n := by
    unfold onePointModelStageRadius
    exact le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2)
  exact
    ⟨((le_max_left r₁ r₂).trans hmaxn).trans hnrad,
      ((le_max_right r₁ r₂).trans hmaxn).trans hnrad⟩

/--
Compact subsets whose model image avoids both marked model ends are eventually
contained in the pulled-back model stages.
-/
theorem exists_bound_for_compact_subset_pulledBackModelStage
    {X : Type*} [TopologicalSpace X] (e : X ≃ₜ OnePoint ℂ)
    {K : Set X} (hK : IsCompact K)
    (hsource :
      ∀ x, x ∈ K → e x ∈ identityChart.source ∩ inversionChart.source) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K ⊆ pulledBackModelStage e n := by
  have hmaps_id : MapsTo (fun x => e x) K identityChart.source :=
    fun x hx => (hsource x hx).1
  have hcont_id : ContinuousOn (fun x => identityChart (e x)) K :=
    identityChart.continuousOn.comp e.continuous.continuousOn hmaps_id
  have hcompact_id :
      IsCompact ((fun x => identityChart (e x)) '' K) :=
    hK.image_of_continuousOn hcont_id
  obtain ⟨r_id, hr_id⟩ := hcompact_id.isBounded.subset_ball (0 : ℂ)
  have hmaps_inv : MapsTo (fun x => e x) K inversionChart.source :=
    fun x hx => (hsource x hx).2
  have hcont_inv : ContinuousOn (fun x => inversionChart (e x)) K :=
    inversionChart.continuousOn.comp e.continuous.continuousOn hmaps_inv
  have hcompact_inv :
      IsCompact ((fun x => inversionChart (e x)) '' K) :=
    hK.image_of_continuousOn hcont_inv
  obtain ⟨r_inv, hr_inv⟩ := hcompact_inv.isBounded.subset_ball (0 : ℂ)
  obtain ⟨N, hN⟩ := exists_nat_for_modelStageRadius_ge r_id r_inv
  refine ⟨N, ?_⟩
  intro n hn x hx
  have hsrc := hsource x hx
  have hradius := hN n hn
  unfold pulledBackModelStage onePointModelStage
  exact
    ⟨⟨hsrc.1,
        Metric.ball_subset_ball hradius.1
          (hr_id (mem_image_of_mem (fun x => identityChart (e x)) hx))⟩,
      ⟨hsrc.2,
        Metric.ball_subset_ball hradius.2
          (hr_inv (mem_image_of_mem (fun x => inversionChart (e x)) hx))⟩⟩

end

end JacobianChallenge.HolomorphicForms
