import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Jacobian.Periods.IntegralOneCycle

/-!
# `realDimSingularH1` component-dual dimension bridge

Tiny standalone module exposing only the ℕ-valued surrogate
`realDimSingularH1 X` — the real dimension of the singular cohomology
`H¹_sing(X, ℝ)` of a topological space `X` (in degree 1).

This module exists to break a potential import cycle between the
**de Rham theorem** decomposition (`DeRhamComparisonMap.lean`) and
its consumer (`DeRhamSingular.lean`): both need access to the same
ℕ-valued bridge variable but neither should depend on the other.

In the current project substrate this dimension is grounded as the
real finrank of the ℤ-linear dual of integral one-cycles. This is the
universal-coefficient target that downstream files compare against.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open JacobianChallenge.Periods

/-- Real dimension of
`Hom_ℤ(H₁(X, ℤ), ℝ)`, the singular cohomology `H¹_sing(X, ℝ)` of `X`
in degree 1. Used as the intermediate ℕ-valued bridge between
de Rham (analytic) and integer homology (topological). -/
noncomputable def realDimSingularH1
    (X : Type*) [TopologicalSpace X] : ℕ :=
  Module.finrank ℝ (IntegralOneCycle X →ₗ[ℤ] ℝ)

end JacobianChallenge.HolomorphicForms
