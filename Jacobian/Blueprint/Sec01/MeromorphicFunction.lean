import Jacobian.Blueprint.Sec01.VanishingOrder
import Mathlib.Topology.Compactification.OnePoint.Basic

/-! Blueprint: `def:meromorphic-function` in
`tex/sections/01-compact-riemann-surfaces.tex`.

The set `Mer(X)` of meromorphic functions on a compact Riemann surface,
viewed as the field of meromorphic germ sections. -/

namespace JacobianChallenge.Blueprint

open scoped Manifold

/-- The type of meromorphic functions on a compact Riemann surface `X`.

Approximated as a `Type _` placeholder until the meromorphic-germ-sheaf
gluing is in place; the blueprint asserts it is a field with `ℂ` embedded
as constants. -/
-- TODO: pin down to actual meromorphic-germ-sheaf construction once
-- the global field-of-fractions API on a Riemann surface is built.
def MeromorphicFunctionType (X : Type*) [TopologicalSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X] :
    Type _ :=
  X → OnePoint ℂ

end JacobianChallenge.Blueprint
