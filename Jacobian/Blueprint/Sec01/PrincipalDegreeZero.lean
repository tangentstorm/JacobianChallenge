import Jacobian.Blueprint.Sec01.PrincipalDivisor
import Jacobian.Blueprint.Sec01.DivisorDegree

/-! Blueprint: `thm:principal-degree-zero` in
`tex/sections/01-compact-riemann-surfaces.tex`.

For every nonzero meromorphic function `f` on a compact Riemann surface,
`deg((f)) = 0`. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold

/-- Principal divisors have degree zero.

Now that `principalDivisor` is the genuine `Σ_p ord_p(f) · p`
`Finsupp.onFinset` (`Sec01/PrincipalDivisor.lean`), the previous
`show … 0` definitional trick no longer applies. The classical proof
(residue theorem / argument principle) is the DECOMPOSE node flagged
in `ref/scope-out.md`; until those sub-leaves land we leave this
theorem as a sorry-bearing frontier obligation.

BLOCKER: needs `vanishingOrder`-sum-equals-zero (residue theorem on
a compact Riemann surface). The current `MeromorphicFunctionType`
placeholder lacks the meromorphic-germ-sheaf structure required to
formulate the residue identity, and the chart-local Laurent residue
sum is itself a frontier sub-leaf. -/
theorem principal_degree_zero
    (X : Type*) [TopologicalSpace X] [ConnectedSpace X] [CompactSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) :
    Divisor.degree (principalDivisor X f) = 0 := by
  sorry

end JacobianChallenge.Blueprint
