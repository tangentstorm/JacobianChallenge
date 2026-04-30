import Jacobian.ComplexTorus.Defs
import Jacobian.ComplexTorus.TransitionLocallyTranslate
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# `ContDiffOn ω` for the chart-transition map

Queue B sibling. Fourth sub-lemma toward `IsManifold`. Promotes the
locally-translation property (`TransitionLocallyTranslate`) to a
genuine `ContDiffOn ℂ ω` statement on the chart-overlap region.

At each point of the overlap, the transition agrees with the
`ContDiff ℂ ω` translation `y ↦ y + g` (for a locally fixed `g ∈
Λ.subgroup`) on a neighborhood. Thus by
`ContDiffWithinAt.congr_of_eventuallyEq`, the transition is
`ContDiffWithinAt` at each overlap point, and pointwise
`ContDiffWithinAt` is the definition of `ContDiffOn`.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The chart transition `localSection_v₂ ∘ mk` is `ContDiffOn ℂ ω`
on the chart-overlap region. -/
lemma contDiffOn_localSection_mk
    (Λ : FullComplexLattice V) (v₁ v₂ : V) {δ r : ℝ}
    (hδpos : 0 < δ)
    (hr_lt : r < δ / 2)
    (hiso : ∀ g ∈ Λ.subgroup, g ≠ 0 → δ ≤ ‖g‖) :
    ContDiffOn ℂ (⊤ : WithTop ℕ∞) (fun y : V => localSection Λ v₂ r (mk V Λ y))
      (Metric.ball v₁ r ∩ mk V Λ ⁻¹' (mk V Λ '' Metric.ball v₂ r)) := by
  intro x hx
  obtain ⟨U, hU_mem, hU_eq⟩ :=
    localSection_mk_locally_translate Λ v₁ v₂ hδpos hr_lt hiso hx
  -- The local translation function (constant `g` depending on `x`).
  set g : V := localSection Λ v₂ r (mk V Λ x) - x with g_def
  -- `fun y => y + g` is `ContDiff ℂ ω`.
  have htrans : ContDiff ℂ (⊤ : WithTop ℕ∞) (fun y : V => y + g) :=
    contDiff_id.add contDiff_const
  -- Hence `ContDiffWithinAt` everywhere; restrict to our `s` and base point `x`.
  have htrans_within : ContDiffWithinAt ℂ (⊤ : WithTop ℕ∞)
      (fun y : V => y + g)
      (Metric.ball v₁ r ∩ mk V Λ ⁻¹' (mk V Λ '' Metric.ball v₂ r)) x :=
    htrans.contDiffAt.contDiffWithinAt
  -- Eventually-equal: on `U` the transition equals the translation.
  have heqOn : (fun y : V => localSection Λ v₂ r (mk V Λ y))
      =ᶠ[nhdsWithin x
        (Metric.ball v₁ r ∩ mk V Λ ⁻¹' (mk V Λ '' Metric.ball v₂ r))]
      (fun y : V => y + g) := by
    filter_upwards [hU_mem] with y hy using hU_eq y hy
  -- Equal at the base point.
  have hxU : x ∈ U := mem_of_mem_nhdsWithin hx hU_mem
  have hxbase :
      (fun y : V => localSection Λ v₂ r (mk V Λ y)) x =
        (fun y : V => y + g) x := by
    simpa using hU_eq x hxU
  exact htrans_within.congr_of_eventuallyEq heqOn hxbase

end JacobianChallenge.ComplexTorus
