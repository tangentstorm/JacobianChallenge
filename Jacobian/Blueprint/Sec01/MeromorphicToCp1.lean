import Jacobian.Blueprint.Sec01.MeromorphicFunction
import Mathlib.Topology.Compactification.OnePoint.Basic

/-! Blueprint: `def:meromorphic-to-cp1` in
`tex/sections/01-compact-riemann-surfaces.tex`.

The associated map `f̂ : X → ℂ ∪ {∞}` to the Riemann sphere from a nonzero
meromorphic function. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold

/-- The associated map to `OnePoint ℂ` (the Riemann sphere) from a
meromorphic function: simply the underlying set function `f.toFun`. -/
noncomputable def meromorphicToCp1
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) : X → OnePoint ℂ :=
  f.toFun

/-- Continuity of the CP¹ lift of a meromorphic function.

Body: `meromorphicToCp1 X f := f.toFun`, and `f.toFun_continuous` is the
relevant `Continuous` field of the `MeromorphicFunctionType` structure.

Used by `liftToCp1_branchedCoverData` (sub-leaf 2 of
`thm:principal-degree-zero`) to feed
`Sec02/BranchedDegree.lean` leaf 8
(`branchedCoverData_of_nonconstant_holomorphic`). -/
theorem liftToCp1_continuous
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    (f : MeromorphicFunctionType X) (_hholo : True) :
    Continuous (meromorphicToCp1 X f) :=
  f.toFun_continuous

end JacobianChallenge.Blueprint
