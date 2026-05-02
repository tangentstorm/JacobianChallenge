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

The "nonzero meromorphic" hypothesis matches `divisor_discrete`:
`[ConnectedSpace X]` (Riemann-surface convention), pointwise meromorphy
`hf_mero`, and the existential `h_nontriv` encoding "not identically
zero". Connectedness propagates `h_nontriv` to "finite vanishing order
everywhere" inside `divisor_discrete`. -/
theorem divisor_finite_support
    (X : Type*) [TopologicalSpace X] [ConnectedSpace X] [CompactSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : X → ℂ)
    (hf_mero : ∀ q : X, MeromorphicAtX f q)
    (h_nontriv : ∃ p : X, vanishingOrder X p f ≠ ⊤) :
    Set.Finite {q : X | vanishingOrder X q f ≠ 0} := by
  by_contra h
  rw [Set.not_finite] at h
  obtain ⟨x, hx⟩ := h.exists_accPt_principal
  exact divisor_discrete X f hf_mero h_nontriv x hx

end JacobianChallenge.Blueprint
