import Jacobian.Blueprint.Sec01.Divisor
import Jacobian.Blueprint.Sec01.MeromorphicFunction
import Jacobian.Blueprint.Sec01.DivisorFiniteSupport

/-! Blueprint: `def:principal-divisor` in
`tex/sections/01-compact-riemann-surfaces.tex`.

The principal divisor `(f) := Σ_p ord_p(f) · p` of a nonzero meromorphic
function. Combined finiteness of the support comes from
`lem:divisor-finite-support`. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold

/-- The principal divisor of a (nonzero) meromorphic function. -/
noncomputable def principalDivisor
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (_f : MeromorphicFunctionType X) : Divisor X :=
  sorry

end JacobianChallenge.Blueprint
