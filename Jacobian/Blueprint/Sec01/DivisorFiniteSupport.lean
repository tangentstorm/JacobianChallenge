import Jacobian.Blueprint.Sec01.DivisorDiscrete
import Mathlib.Topology.Compactness.Compact

/-! Blueprint: `lem:divisor-finite-support` in
`tex/sections/01-compact-riemann-surfaces.tex`.

Compactness gives finite divisor support: a subset of a compact space
with no accumulation point is finite. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold
open JacobianChallenge.HolomorphicForms.VanishingOrder

/-- For a nonzero meromorphic function on a compact Riemann surface, the
set of points with nonzero vanishing order is finite.

The "nonzero meromorphic" hypothesis is encoded pointwise (matching
`divisor_discrete`): `f` is meromorphic at every point and has finite
vanishing order at every point. -/
theorem divisor_finite_support
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : X → ℂ)
    (hf_mero : ∀ q : X, MeromorphicAtX f q)
    (hf_finite : ∀ q : X, vanishingOrder X q f ≠ ⊤) :
    Set.Finite {q : X | vanishingOrder X q f ≠ 0} := by
  by_contra h
  rw [Set.not_finite] at h
  obtain ⟨x, hx⟩ := h.exists_accPt_principal
  exact divisor_discrete X f hf_mero hf_finite x hx

end JacobianChallenge.Blueprint
