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
    (_f : MeromorphicFunctionType X) : Divisor X := by
  /- PROOF SKETCH:
  1. Define coefficient at `p` as `vanishingOrder X p _f`.
  2. Use `divisor_finite_support` to show only finitely many nonzero coefficients.
  3. Package coefficients + finite-support proof into `Divisor X`.
  4. Keep this as a named blueprint constructor until production divisor API
     (`Finsupp`/`Divisor`) is finalized upstream.
  -/
  sorry

end JacobianChallenge.Blueprint
