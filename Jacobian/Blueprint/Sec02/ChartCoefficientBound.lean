import Jacobian.Blueprint.Sec02.HolomorphicSupNorm
import Jacobian.HolomorphicForms.CompactRiemannSurface
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-! # Blueprint stub: `lem:chart-coefficient-bound`

Section 2 of `tex/sections/02-holomorphic-forms-and-genus.tex`.

Local coefficient bound on a chart `e : OpenPartialHomeomorph X ℂ` in
the atlas: there is a chart-local constant `C ≥ 0` such that for every
holomorphic 1-form `ω` and every `x ∈ e.source`, the fiber norm
`‖ω x‖_x` is bounded by `C * ‖ω‖`. The constant `C` depends only on the
chart and the partition-of-unity weight, not on `ω`. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold
open JacobianChallenge.HolomorphicForms

/-- Chart-local fiber-norm bound: for each chart `e` in the atlas of
`X`, there is a constant `C ≥ 0` such that the fiber norm of any
holomorphic 1-form on `e.source` is bounded by `C` times the global
sup norm.

With the integrator's choice
`cotangentFiberNorm X ⟨x, v⟩ = ‖v‖`
and
`holomorphicSupNorm X ω = ⨆ x, cotangentFiberNormAt X x (ω.1 x)`,
the constant `C = 1` works: the fiber norm at any point is bounded by
the iSup, and the chart `e` plays no role beyond delineating the open
set on which the bound is asserted. The argument is the standard
`le_ciSup` once `BddAbove` of the range is known; that finiteness is
supplied by the upstream
`holomorphicOneForm_fiberNorm_continuous` (compactness ⇒ bounded image
of a continuous fiber-norm function), which is sorry-blocked upstream
but treated here as a black box. -/
theorem chart_coefficient_bound
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    (e : OpenPartialHomeomorph X ℂ) (_he : e ∈ atlas ℂ X) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ω : HolomorphicOneForm ℂ X) (x : X),
      x ∈ e.source →
        cotangentFiberNormAt X x (ω.1 x) ≤ C * holomorphicSupNorm X ω := by
  refine ⟨1, zero_le_one, fun ω x _hx => ?_⟩
  have hbdd : BddAbove (Set.range fun y => ‖ω.1 y‖) :=
    SectionSupNorm.bddAbove_range_norm (holomorphicOneForm_hcompat X) ω
  have hle : ‖ω.1 x‖ ≤ ⨆ y : X, ‖ω.1 y‖ := le_ciSup hbdd x
  show cotangentFiberNorm X ⟨x, ω.1 x⟩ ≤ 1 * holomorphicSupNorm X ω
  rw [one_mul]
  exact hle

end JacobianChallenge.Blueprint
