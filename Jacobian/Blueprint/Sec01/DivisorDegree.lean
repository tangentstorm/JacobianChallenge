import Jacobian.Blueprint.Sec01.Divisor
import Mathlib.Data.Finsupp.Weight

/-! Blueprint: `def:divisor-degree` in
`tex/sections/01-compact-riemann-surfaces.tex`.

The degree map `Div(X) → ℤ` summing all coefficients. -/

namespace JacobianChallenge.Blueprint

/-- The degree of a divisor: the sum of its coefficients.
Defined as `Finsupp.degree`. -/
noncomputable def Divisor.degree {X : Type*} : Divisor X →+ ℤ :=
  Finsupp.degree

end JacobianChallenge.Blueprint
