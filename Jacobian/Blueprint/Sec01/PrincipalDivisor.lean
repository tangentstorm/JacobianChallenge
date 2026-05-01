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

/-- The principal divisor of a (nonzero) meromorphic function.

Placeholder: returns `0`. Two pieces of upstream API need to thicken
before the genuine `Σ_p ord_p(f) · p` Finsupp can be assembled here.
First, `MeromorphicFunctionType X` is currently `X → OnePoint ℂ`, so
extracting the underlying `X → ℂ` that `vanishingOrder` and
`divisor_finite_support` consume needs a fixed projection convention
(e.g. `(_f x).getD 0`). Second, `divisor_finite_support` requires
`_hf_nonzero : ∃ x, f x ≠ 0`, which this signature does not carry — a
nonzero predicate or subtype on `MeromorphicFunctionType` will need to
land first. Until then `0` is a sound default: the zero meromorphic
function legitimately has the zero principal divisor, and downstream
consumers that want the genuine principal divisor will pattern-match
on the (eventually) richer `MeromorphicFunctionType`. -/
noncomputable def principalDivisor
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (_f : MeromorphicFunctionType X) : Divisor X :=
  0

end JacobianChallenge.Blueprint
