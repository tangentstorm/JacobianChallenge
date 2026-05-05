import Mathlib.AlgebraicTopology.SingularSet

/-!
# Stage A — Singular simplex (core type, dependency-light)

The bare type `SingularSimplex X n = C(Δⁿ, X)` along with the standard
topological `n`-simplex `stdSimplex n`.  This file deliberately does not
depend on `Jacobian.Periods.*` so it can be imported by R4
(`Jacobian.Analysis.DeRham`) without dragging in the surface-classification
sub-tree.

The richer prism-operator API and the homotopy-invariance theorems live in
`Jacobian.StageA.PrismOperator`, which imports this module.
-/

namespace JacobianChallenge.StageA

/-- The standard topological `n`-simplex `Δⁿ ⊆ ℝ^{n+1}`. -/
noncomputable abbrev stdSimplex (n : ℕ) : TopCat := SimplexCategory.toTop.obj (.mk n)

/-- A singular `n`-simplex in `X`: a continuous map `Δⁿ → X`. -/
noncomputable def SingularSimplex (X : Type) [TopologicalSpace X] (n : ℕ) : Type :=
  C(stdSimplex n, X)

end JacobianChallenge.StageA
