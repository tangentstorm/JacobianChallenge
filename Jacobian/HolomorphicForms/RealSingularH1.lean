import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# `realDimSingularH1` opaque (frontier ℕ-bridge)

Tiny standalone module exposing only the opaque ℕ
`realDimSingularH1 X` — the real dimension of the singular cohomology
`H¹_sing(X, ℝ)` of a topological space `X` (in degree 1).

This module exists to break a potential import cycle between the
**de Rham theorem** decomposition (`DeRhamComparisonMap.lean`) and
its consumer (`DeRhamSingular.lean`): both need access to the same
ℕ-valued bridge variable but neither should depend on the other.

No declarations here have semantic content; they are purely the
ℕ-valued frontier symbol.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold

/-- **Frontier ℕ-valued opaque.** Real dimension of
`Hom_ℤ(H₁(X, ℤ), ℝ)`, the singular cohomology `H¹_sing(X, ℝ)` of `X`
in degree 1. Used as the intermediate ℕ-valued bridge between
de Rham (analytic) and integer homology (topological). -/
noncomputable opaque realDimSingularH1
    (X : Type) [TopologicalSpace X] : ℕ

end JacobianChallenge.HolomorphicForms
