import Jacobian.HolomorphicForms.StageExhaustion
import Mathlib.Data.Fintype.EquivFin

/-!
# Compact frontier chart covers

This module packages the canonical manifold-chart cover of a compact stage
frontier as finite `StageBoundaryChartData`.
-/

namespace JacobianChallenge.HolomorphicForms

open Filter Set
open scoped Topology

noncomputable section

/--
A compact frontier admits finite `StageBoundaryChartData` by extracting a
finite subcover from the canonical chart-source neighborhoods.
-/
theorem stageBoundaryChartData_of_compact_frontier
    {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {stage : Set X}
    (hfrontier : IsCompact (frontier stage)) :
    Nonempty (StageBoundaryChartData X stage) := by
  classical
  obtain ⟨t, _ht_frontier, hcover⟩ :=
    hfrontier.elim_nhds_subcover
      (fun x : X => (chartAt ℂ x).source)
      (by
        intro x _hx
        exact (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x))
  let center : Fin t.card → X := fun i => (t.equivFin.symm i : t)
  refine
    ⟨{ ChartIndex := Fin t.card
       chart_fintype := by infer_instance
       chart := fun i => chartAt ℂ (center i)
       boundaryPiece := fun i => frontier stage ∩ (chartAt ℂ (center i)).source
       boundaryPiece_subset_source := ?_
       boundaryPiece_subset_frontier := ?_
       frontier_subset_boundaryPieces := ?_ }⟩
  · intro i y hy
    exact hy.2
  · intro i y hy
    exact hy.1
  · intro y hy
    rcases mem_iUnion₂.mp (hcover hy) with ⟨x, hxt, hy_source⟩
    refine mem_iUnion.mpr ⟨t.equivFin ⟨x, hxt⟩, ?_⟩
    simpa [center] using And.intro hy hy_source

end

end JacobianChallenge.HolomorphicForms
