import Jacobian.Blueprint.Sec01.MeromorphicToCp1

/-! Blueprint: `thm:meromorphic-as-cp1-map` in
`tex/sections/01-compact-riemann-surfaces.tex`.

The bijection between nonzero meromorphic functions on `X` and
nonconstant holomorphic maps `X → ℂ ∪ {∞}`. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold

/-- Stub for the meromorphic↔Cp1-map bijection. The current statement is
phrased as nonconstancy of the associated map; the full bijection
requires holomorphic-map theory on `OnePoint ℂ`. -/
theorem meromorphic_as_cp1_map
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X)
    (_hf_nonconstant : ¬ ∃ c : OnePoint ℂ, ∀ x, f x = c) :
    ¬ ∃ c : OnePoint ℂ, ∀ x, meromorphicToCp1 X f x = c := by
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
