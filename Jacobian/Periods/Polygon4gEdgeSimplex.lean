import Jacobian.Periods.Polygon4gEdgeLoops
import Mathlib.Analysis.Convex.StdSimplex

/-!
# Edge loops as singular 1-simplices

For each `i : Fin (2*(g+1))`, this file packages the edge loop
`edgeContMap g i : C(unitInterval, Polygon4g (g+1))` from
`Jacobian.Periods.Polygon4gEdgeLoops` as a continuous map from the
standard topological 1-simplex `stdSimplex ℝ (Fin 2)` — the shape
expected by Mathlib's singular homology API
(`TopCat.toSSetObjEquiv`).

The conversion uses the existing Mathlib homeomorphism
`stdSimplexHomeomorphUnitInterval : stdSimplex ℝ (Fin 2) ≃ₜ
unitInterval` (Mathlib `Analysis.Convex.StdSimplex`).

## Status

Sorry-free. This is Phase 1.5 of the cellular Hurewicz infrastructure
plan in `ref/plans/cellular-hurewicz-plan.md`. The next phase
(`SingularChainElement`) consumes `edgeSimplex g i` to produce a
chain-complex element.
-/

namespace JacobianChallenge.Periods

open Set unitInterval

/-- The continuous map version of `stdSimplexHomeomorphUnitInterval`,
useful for composing with arrows in `C(unitInterval, _)`. -/
noncomputable def stdSimplexToUnitInterval :
    C(stdSimplex ℝ (Fin 2), unitInterval) :=
  ⟨stdSimplexHomeomorphUnitInterval, stdSimplexHomeomorphUnitInterval.continuous⟩

/-- The `i`-th edge of the genus-`(g+1)` polygon as a singular
1-simplex (continuous map from the standard topological 1-simplex). -/
noncomputable def edgeSimplex (g : ℕ) (i : Fin (2 * (g + 1))) :
    C(stdSimplex ℝ (Fin 2), Polygon4g (g + 1)) :=
  (edgeContMap g i).comp stdSimplexToUnitInterval

@[simp] lemma edgeSimplex_apply (g : ℕ) (i : Fin (2 * (g + 1)))
    (s : stdSimplex ℝ (Fin 2)) :
    edgeSimplex g i s =
      Polygon4g.mk (g + 1)
        (boundaryParam (g + 1) (edgeArcIdx g i)
          (stdSimplexHomeomorphUnitInterval s).val) := by
  simp [edgeSimplex, stdSimplexToUnitInterval, edgeContMap]

/-- The two vertices of `stdSimplex ℝ (Fin 2)`: `single i 1` for `i ∈ Fin 2`. -/
noncomputable def stdSimplexVertex (i : Fin 2) : stdSimplex ℝ (Fin 2) :=
  ⟨_, single_mem_stdSimplex _ i⟩

@[simp] lemma stdSimplexHomeomorphUnitInterval_vertex_zero :
    stdSimplexHomeomorphUnitInterval (stdSimplexVertex 0) = 0 :=
  stdSimplexHomeomorphUnitInterval_zero

@[simp] lemma stdSimplexHomeomorphUnitInterval_vertex_one :
    stdSimplexHomeomorphUnitInterval (stdSimplexVertex 1) = 1 :=
  stdSimplexHomeomorphUnitInterval_one

/-- The "0 vertex" of `edgeSimplex g i`: the disk-boundary point at the
start of arc `edgeArcIdx g i`, modulo side-pairing. -/
lemma edgeSimplex_vertex_zero (g : ℕ) (i : Fin (2 * (g + 1))) :
    edgeSimplex g i (stdSimplexVertex 0) =
      Polygon4g.mk (g + 1) (boundaryParam (g + 1) (edgeArcIdx g i) 0) := by
  simp [edgeSimplex, stdSimplexToUnitInterval, edgeContMap, stdSimplexVertex,
    stdSimplexHomeomorphUnitInterval_zero]

/-- The "1 vertex" of `edgeSimplex g i`: the disk-boundary point at the
end of arc `edgeArcIdx g i`, modulo side-pairing. -/
lemma edgeSimplex_vertex_one (g : ℕ) (i : Fin (2 * (g + 1))) :
    edgeSimplex g i (stdSimplexVertex 1) =
      Polygon4g.mk (g + 1) (boundaryParam (g + 1) (edgeArcIdx g i) 1) := by
  simp [edgeSimplex, stdSimplexToUnitInterval, edgeContMap, stdSimplexVertex,
    stdSimplexHomeomorphUnitInterval_one]

end JacobianChallenge.Periods
