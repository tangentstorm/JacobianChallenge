import Jacobian.Blueprint.Sec01.PrincipalDivisor
import Mathlib.Algebra.Group.Subgroup.Defs
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-! Blueprint: `def:principal-divisors` in
`tex/sections/01-compact-riemann-surfaces.tex`.

The subgroup of principal divisors `Prin(X) ⊆ Div(X)`. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold

/-- The subgroup of principal divisors. -/
noncomputable def principalDivisors
    (X : Type*) [TopologicalSpace X] [ConnectedSpace X] [CompactSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X] :
    AddSubgroup (Divisor X) :=
  AddSubgroup.closure (Set.range (principalDivisor X))

end JacobianChallenge.Blueprint
