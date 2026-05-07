import Jacobian.ComplexTorus.Defs
import Jacobian.ComplexTorus.LocalSectionContinuous

/-!
# Continuity of `x ↦ localSection_v₂ (mk x) - x`

Queue B sibling. Second sub-lemma toward `IsManifold`. The function
mapping each `x` in the chart-overlap region to the difference
`localSection Λ v₂ r (mk x) - x` is continuous on that overlap.

This continuity, combined with the algebraic fact that the
difference lands in `Λ.subgroup` (`TransitionSubMem`) and the
discreteness of `Λ.subgroup` (next step), implies that the
difference is locally constant on the overlap. From there the chart
transition becomes locally a translation by a fixed lattice
element, hence `C^ω`.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

omit [NormedSpace ℂ V] in
/-- The map `x ↦ localSection Λ v₂ r (mk x) - x` is continuous on the
chart-overlap region. -/
lemma continuousOn_localSection_mk_sub
    (Λ : FullComplexLattice V) (v₁ v₂ : V) {δ r : ℝ}
    (hr_lt : r < δ / 2)
    (hiso : ∀ g ∈ Λ.subgroup, g ≠ 0 → δ ≤ ‖g‖) :
    ContinuousOn (fun x : V => localSection Λ v₂ r (mk V Λ x) - x)
      (Metric.ball v₁ r ∩ mk V Λ ⁻¹' (mk V Λ '' Metric.ball v₂ r)) := by
  have hmk : ContinuousOn (mk V Λ)
      (Metric.ball v₁ r ∩ mk V Λ ⁻¹' (mk V Λ '' Metric.ball v₂ r)) :=
    QuotientAddGroup.continuous_mk.continuousOn
  have hsec : ContinuousOn (localSection Λ v₂ r) (mk V Λ '' Metric.ball v₂ r) :=
    continuousOn_localSection Λ v₂ hr_lt hiso
  have hcomp : ContinuousOn (fun x : V => localSection Λ v₂ r (mk V Λ x))
      (Metric.ball v₁ r ∩ mk V Λ ⁻¹' (mk V Λ '' Metric.ball v₂ r)) := by
    refine hsec.comp hmk ?_
    intro x hx
    exact hx.2
  exact hcomp.sub continuousOn_id

end JacobianChallenge.ComplexTorus
