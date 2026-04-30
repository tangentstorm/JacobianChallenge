import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-! Blueprint: `def:cotangent-fiber-norm` in
`tex/sections/02-holomorphic-forms-and-genus.tex`.

A continuous fiber norm `‖·‖_x` on the cotangent bundle obtained from a
holomorphic atlas plus a partition-of-unity weight. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold

/-- Stub for the continuous fiber norm on the cotangent bundle of a
complex manifold. The current type is `X → ℝ`, taking a base point to
the norm-of-cotangent-vector at that point — abstracted away because the
project-side fiber-norm API is not stable yet. -/
-- TODO: pin down to `ContinuousLinearMap.norm` on cotangent fibers
-- once the `CotangentSpace` API in `Jacobian.HolomorphicForms.CotangentBundle`
-- is exposed at the top level.
noncomputable def cotangentFiberNorm
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    X → ℝ := sorry

end JacobianChallenge.Blueprint
