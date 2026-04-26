import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Geometry.Manifold.ChartedSpace

/-!
# Lebesgue radius for a chart-source cover

Queue D scaffolding. The Lebesgue number lemma applied to a continuous
map `γ : C(K, X)` from a compact metric space into a charted space:
there exists `δ > 0` such that every `δ`-ball in `K` lands inside a
single chart source.

This is the key combinatorial input to the multi-chart path
integration: combined with a partition of `[0, 1]` of mesh `< δ`,
each sub-path lands inside a single chart and can be integrated via
`pathIntegralInChart`.
-/

namespace JacobianChallenge.Periods

open Set Metric

/-- For a continuous map `γ` from a compact metric space `K` into a
charted space `X`, there is a Lebesgue radius `δ > 0` such that every
`δ`-ball in `K` is contained in some chart's preimage source.

This is a direct application of `lebesgue_number_lemma_of_metric`
to the cover of `X` by chart sources. -/
lemma exists_lebesgue_radius_chart
    {K : Type*} [MetricSpace K] [CompactSpace K]
    (E : Type*) [TopologicalSpace E]
    (X : Type*) [TopologicalSpace X] [ChartedSpace E X]
    (γ : C(K, X)) :
    ∃ δ > 0, ∀ t : K, ∃ x : X, ball t δ ⊆ γ ⁻¹' (chartAt E x).source := by
  have hCover : (univ : Set K) ⊆ ⋃ (x : X), γ ⁻¹' (chartAt E x).source := by
    intro t _
    refine mem_iUnion.mpr ⟨γ t, ?_⟩
    exact ChartedSpace.mem_chart_source (γ t)
  have hOpen : ∀ (x : X), IsOpen (γ ⁻¹' (chartAt E x).source) :=
    fun x => (chartAt E x).open_source.preimage γ.continuous
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    lebesgue_number_lemma_of_metric isCompact_univ hOpen hCover
  refine ⟨δ, hδ_pos, ?_⟩
  intro t
  exact hδ t (mem_univ _)

end JacobianChallenge.Periods
