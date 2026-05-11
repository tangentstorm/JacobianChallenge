import Jacobian.ComplexTorus.Defs
import Jacobian.ComplexTorus.Chart
import Jacobian.ComplexTorus.IsolationAtZero
import Mathlib.Geometry.Manifold.ChartedSpace

/-!
# Charted-space instance on the complex torus

Queue B sibling. With `chartAtBall` in place we can wire the
per-point charts into a `ChartedSpace V (V ⧸ Λ.subgroup)` instance.

Plan:

- For each quotient point `q`, pick a representative `v` of `q`
  via `Function.surjInv` (which uses `Classical.choice` internally).
- Extract a single isolation radius `δ > 0` from
  `Λ.isDiscrete` and use chart radius `δ / 4` uniformly.
- Build the chart at `q` as `chartAtBall Λ v hr_lt hiso`.
- The atlas is the range of `chartAt`.

The "uniform" chart radius keeps the construction simple. A real
mathlib-bound treatment would prefer either a global δ derived once
or per-point optimal radii.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The chart at a quotient point, picking a representative via
`Function.surjInv (mk_surjective V Λ)` and a global isolation
radius `δ > 0`. -/
noncomputable def chartAtPoint (Λ : FullComplexLattice V)
    (q : quotient V Λ) :
    OpenPartialHomeomorph (quotient V Λ) V :=
  let v : V := Function.surjInv (mk_surjective V Λ) q
  let data := exists_pos_le_norm_of_discreteTopology (V := V) Λ.subgroup
  let δ : ℝ := data.choose
  let δpos : 0 < δ := data.choose_spec.1
  let hiso : ∀ g ∈ Λ.subgroup, g ≠ 0 → δ ≤ ‖g‖ := data.choose_spec.2
  chartAtBall Λ v (show (δ : ℝ) / 4 < δ / 2 by linarith) hiso

/-- Membership of a quotient point in its own chart's source. -/
lemma mem_chartAtPoint_source (Λ : FullComplexLattice V)
    (q : quotient V Λ) :
    q ∈ (chartAtPoint Λ q).source := by
  unfold chartAtPoint
  -- source = mk V Λ '' Metric.ball v r where v is the representative
  set v : V := Function.surjInv (mk_surjective V Λ) q
  have hmk : mk V Λ v = q :=
    Function.surjInv_eq (mk_surjective V Λ) q
  set data := exists_pos_le_norm_of_discreteTopology (V := V) Λ.subgroup
  set δ : ℝ := data.choose
  have δpos : 0 < δ := data.choose_spec.1
  -- The source of `chartAtBall Λ v _ _` is `mk V Λ '' Metric.ball v (δ / 4)`.
  -- Need: q ∈ mk V Λ '' Metric.ball v (δ / 4).
  -- v ∈ Metric.ball v (δ / 4) since δ / 4 > 0, and mk V Λ v = q.
  refine ⟨v, ?_, hmk⟩
  rw [Metric.mem_ball, dist_self]
  linarith

/-- The complex torus is a charted space modeled on the ambient
finite-dimensional complex vector space. -/
noncomputable instance complexTorusChartedSpace
    (Λ : FullComplexLattice V) : ChartedSpace V (quotient V Λ) where
  atlas := Set.range (chartAtPoint Λ)
  chartAt := chartAtPoint Λ
  mem_chart_source q := mem_chartAtPoint_source Λ q
  chart_mem_atlas q := ⟨q, rfl⟩

end JacobianChallenge.ComplexTorus
