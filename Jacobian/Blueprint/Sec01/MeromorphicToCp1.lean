import Jacobian.Blueprint.Sec01.MeromorphicFunction
import Mathlib.Topology.Compactification.OnePoint.Basic

/-! Blueprint: `def:meromorphic-to-cp1` in
`tex/sections/01-compact-riemann-surfaces.tex`.

The associated map `f̂ : X → ℂ ∪ {∞}` to the Riemann sphere from a nonzero
meromorphic function. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold

/-- The associated map to `OnePoint ℂ` (the Riemann sphere) from a
nonzero meromorphic function. -/
noncomputable def meromorphicToCp1
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) : X → OnePoint ℂ :=
  f

/-- Continuity of the CP¹ lift of a meromorphic function.

Bottom-up content: every meromorphic function on a complex 1-manifold
is continuous when viewed as a map into the one-point compactification
`OnePoint ℂ`, sending each pole to `∞`. The proof factors through the
chart-local Laurent normal form: in a chart at `p`, the map is locally
either holomorphic (regular point), `z ↦ z^e · u(z)` with `u(0) ≠ 0`
(zero of order `e`), or `z ↦ ∞` away from `0` and `∞` at `0` (pole)
— continuity at each chart point is then a standard `OnePoint`
neighbourhood argument.

Used by `liftToCp1_branchedCoverData` (sub-leaf 2 of
`thm:principal-degree-zero`) to feed
`Sec02/BranchedDegree.lean` leaf 8
(`branchedCoverData_of_nonconstant_holomorphic`).

The placeholder `_hholo : True` records the eventual
"`f` is a holomorphic-meromorphic germ" hypothesis once the
meromorphic-germ-sheaf API on `MeromorphicFunctionType` lands; on the
current `X → OnePoint ℂ` placeholder this hypothesis carries no real
content. -/
theorem liftToCp1_continuous
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (_hholo : True) :
    Continuous (meromorphicToCp1 X f) := by
  sorry

end JacobianChallenge.Blueprint
