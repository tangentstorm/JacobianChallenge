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

end JacobianChallenge.Blueprint
