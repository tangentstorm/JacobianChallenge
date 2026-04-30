import Jacobian.Blueprint.Sec01.VanishingOrder
import Mathlib.Topology.Basic

/-! Blueprint: `lem:divisor-discrete` in
`tex/sections/01-compact-riemann-surfaces.tex`.

For a nonzero meromorphic function `f` on a compact Riemann surface `X`,
the set `{p ∈ X : ord_p(f) ≠ 0}` has no accumulation point. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold

/-- The divisor support is discrete: the set of points where the
vanishing order of a nonzero meromorphic function is nonzero has no
accumulation point.

The actual statement here is parameterised on a function `f : X → ℂ`
and the predicate `MeromorphicNonzero f` is left abstract — when the
upstream `MeromorphicAtX` API stabilises we will swap in the real
hypothesis. -/
theorem divisor_discrete
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : X → ℂ) (_hf_nonzero : ∃ x, f x ≠ 0) :
    ∀ p : X, ¬ AccPt p (Filter.principal {q : X | vanishingOrder X q f ≠ 0}) := by
  sorry

end JacobianChallenge.Blueprint
