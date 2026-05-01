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
  -- BLOCKER: the placeholder hypothesis `_hf_nonzero : ∃ x, f x ≠ 0` is
  -- too weak — the statement is FALSE without a real meromorphic hypothesis
  -- and connectedness. Counterexample: X = ℂ ⊔ ℂ, f = 0 on the first copy,
  -- f = 1 on the second; then `_hf_nonzero` holds but S = first copy
  -- accumulates everywhere on it (constant zero has `meromorphicOrderAt = ⊤`).
  -- Need: `MeromorphicAtX f` everywhere (meromorphic on X) AND connectedness
  -- of X (Riemann-surface convention), so the identity principle rules out
  -- `f ≡ 0` on any open subset given `∃ x, f x ≠ 0`. The file's own
  -- docstring marks this as pending: "the predicate `MeromorphicNonzero f`
  -- is left abstract — when the upstream `MeromorphicAtX` API stabilises we
  -- will swap in the real hypothesis." Cannot proceed at this strength.
  sorry

end JacobianChallenge.Blueprint
