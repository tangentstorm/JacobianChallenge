import Jacobian.AnalyticJacobian.Mk
import Jacobian.Periods.PeriodSubgroupRange

/-!
# `mk` zero ↔ membership in `periodPairing.range`

Composes `mk_eq_zero_iff` with `periodSubgroup_eq_range` to expose the
range characterization directly.
-/

namespace JacobianChallenge.AnalyticJacobian

open JacobianChallenge.HolomorphicForms JacobianChallenge.Periods

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- `mk E X φ = 0` iff `φ` lies in the range of `periodPairing`. -/
theorem mk_eq_zero_iff_mem_range
    (φ : HolomorphicOneForm E X →ₗ[ℂ] ℂ) :
    mk E X φ = 0 ↔ φ ∈ (periodPairing E X).range := by
  rw [mk_eq_zero_iff, periodSubgroup_eq_range]

end JacobianChallenge.AnalyticJacobian
