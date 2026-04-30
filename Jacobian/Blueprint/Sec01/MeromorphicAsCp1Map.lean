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
    (hf_nonconstant : ¬ ∃ c : OnePoint ℂ, ∀ x, f x = c) :
    ¬ ∃ c : OnePoint ℂ, ∀ x, meromorphicToCp1 X f x = c :=
  hf_nonconstant

end JacobianChallenge.Blueprint
