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
  /- PROOF SKETCH:
  1. Reduce to local charts and use the corresponding complex-analytic statement
     (isolated zeros/poles, local Laurent expansion, Cauchy estimate, Montel, or
     Riesz representation depending on the node).
  2. Transfer the local analytic estimate/property back through chart-change
     compatibility lemmas from the manifold API.
  3. Conclude the global statement by compactness/finite-subcover and standard
     linear-topological packaging in mathlib (Submodule, FiniteDimensional,
     CompactSpace, Proper, etc.).
  4. This theorem is intentionally left as a named blueprint leaf to be replaced
     by the concrete mathlib-facing implementation once supporting APIs land.
  -/
  sorry

end JacobianChallenge.Blueprint
