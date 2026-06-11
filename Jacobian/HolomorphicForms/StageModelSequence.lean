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

end

end JacobianChallenge.HolomorphicForms
