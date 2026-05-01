import Jacobian.Blueprint.Sec01.PrincipalDivisor
import Jacobian.Blueprint.Sec01.DivisorDegree

/-! Blueprint: `thm:principal-degree-zero` in
`tex/sections/01-compact-riemann-surfaces.tex`.

For every nonzero meromorphic function `f` on a compact Riemann surface,
`deg((f)) = 0`. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold

/-- Principal divisors have degree zero.

On the current placeholder layer this is definitionally trivial:
`principalDivisor X f` is defined as `0 : Divisor X` (see
`Sec01/PrincipalDivisor.lean`), so the degree is `Divisor.degree 0 = 0`
via `map_zero` of the `AddMonoidHom`. Once `principalDivisor` is
upgraded to the genuine `Σ_p ord_p(f) · p` Finsupp, this proof will be
replaced by the classical residue-theorem / argument-principle argument
identified in `ref/scope-out.md` (DECOMPOSE node). -/
theorem principal_degree_zero
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) :
    Divisor.degree (principalDivisor X f) = 0 := by
  show Divisor.degree (0 : Divisor X) = 0
  exact map_zero _

end JacobianChallenge.Blueprint
