import Jacobian.Blueprint.Sec01.DivisorDiscrete
import Mathlib.Topology.Compactness.Compact

/-! Blueprint: `lem:divisor-finite-support` in
`tex/sections/01-compact-riemann-surfaces.tex`.

Compactness gives finite divisor support: a subset of a compact space
with no accumulation point is finite. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold

/-- For a nonzero meromorphic function on a compact Riemann surface, the
set of points with nonzero vanishing order is finite. -/
theorem divisor_finite_support
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : X → ℂ) (_hf_nonzero : ∃ x, f x ≠ 0) :
    Set.Finite {q : X | vanishingOrder X q f ≠ 0} := by
  sorry

end JacobianChallenge.Blueprint
