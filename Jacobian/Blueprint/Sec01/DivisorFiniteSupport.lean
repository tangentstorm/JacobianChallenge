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
