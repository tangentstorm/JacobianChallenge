import Jacobian.Periods.LebesgueChartRadius

/-!
# Per-point chart-ball lemma for continuous maps

Queue D scaffolding. A pointwise variant of
`exists_lebesgue_radius_chart`: rather than producing a single
uniform radius `δ` that works at every point, this lemma asserts
that for a continuous map `γ : C(K, X)` from a metric space to a
charted space, at each point `t : K` there is a chart-ball
neighborhood — a radius `r > 0` and the chart at `γ t` whose source
contains the image `γ (ball t r)`.

Proof sketch:
* `(chartAt E (γ t)).source` is open in `X` (chart-source openness).
* Its preimage under continuous `γ` is open in `K`, contains `t`
  (because `γ t ∈ chart.source` by `mem_chart_source`).
* By `Metric.isOpen_iff`, an open set containing `t` contains some
  `ball t r`.

This is useful as a building block for the multi-chart partition:
the Lebesgue radius lemma packages this uniformly across `K`, but
the pointwise version is sometimes simpler to apply.
-/

namespace JacobianChallenge.Periods

open Metric Set

/-- At each point `t : K` of the source, the continuous map `γ` admits
a chart-ball: a positive radius `r` such that the open ball of radius
`r` around `t` is mapped by `γ` into the chart at `γ t`'s source. -/
lemma exists_chart_ball_at_point
    {K : Type*} [MetricSpace K]
    (E : Type*) [TopologicalSpace E]
    {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
    (γ : C(K, X)) (t : K) :
    ∃ r : ℝ, 0 < r ∧ ball t r ⊆ γ ⁻¹' (chartAt E (γ t)).source := by
  have hopen : IsOpen (γ ⁻¹' (chartAt E (γ t)).source) :=
    (chartAt E (γ t)).open_source.preimage γ.continuous
  have hmem : t ∈ γ ⁻¹' (chartAt E (γ t)).source :=
    ChartedSpace.mem_chart_source (γ t)
  exact Metric.isOpen_iff.mp hopen t hmem

end JacobianChallenge.Periods
