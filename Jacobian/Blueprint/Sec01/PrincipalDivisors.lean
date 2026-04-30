import Jacobian.Blueprint.Sec01.PrincipalDivisor
import Mathlib.Algebra.Group.Subgroup.Defs

/-! Blueprint: `def:principal-divisors` in
`tex/sections/01-compact-riemann-surfaces.tex`.

The subgroup of principal divisors `Prin(X) ⊆ Div(X)`. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold

/-- The subgroup of principal divisors. -/
noncomputable def principalDivisors
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    AddSubgroup (Divisor X) := by
  /- PROOF SKETCH:
  1. Set carrier `{D | ∃ f, principalDivisor X f = D}`.
  2. Prove `0` belongs using the constant nonzero meromorphic function.
  3. Prove closure under addition via `(fg) = (f) + (g)`.
  4. Prove closure under negation via `(f⁻¹) = -(f)`.
  5. Package as `AddSubgroup (Divisor X)`.
  -/
  sorry

end JacobianChallenge.Blueprint
