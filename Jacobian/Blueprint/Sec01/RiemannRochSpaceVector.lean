import Jacobian.Blueprint.Sec01.RiemannRochSpace

/-! Blueprint: `lem:riemann-roch-space-vector` in
`tex/sections/01-compact-riemann-surfaces.tex`.

`L(D)` is a `ℂ`-vector subspace of `Mer(X)`. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold

/-- The Riemann-Roch space carries a `ℂ`-vector space structure (as a
subspace of `Mer(X)`). The actual statement here is a placeholder
asserting existence of such structure. -/
theorem riemann_roch_space_vector
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (_D : Divisor X) :
    -- TODO: replace `True` with `IsAddSubgroup` + `ℂ`-stability
    -- once `MeromorphicFunctionType` carries an additive/scalar
    -- action structure.
    True := by
  trivial

end JacobianChallenge.Blueprint
