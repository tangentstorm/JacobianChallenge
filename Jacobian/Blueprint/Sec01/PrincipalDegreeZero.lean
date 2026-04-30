import Jacobian.Blueprint.Sec01.PrincipalDivisor
import Jacobian.Blueprint.Sec01.DivisorDegree

/-! Blueprint: `thm:principal-degree-zero` in
`tex/sections/01-compact-riemann-surfaces.tex`.

For every nonzero meromorphic function `f` on a compact Riemann surface,
`deg((f)) = 0`. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold

/-- Principal divisors have degree zero. -/
theorem principal_degree_zero
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) :
    Divisor.degree (principalDivisor X f) = 0 := by
  sorry

end JacobianChallenge.Blueprint
