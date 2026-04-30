import Mathlib.Data.Finsupp.Defs
import Mathlib.Algebra.Group.Hom.Defs

/-! Blueprint: `def:divisor` in
`tex/sections/01-compact-riemann-surfaces.tex`.

The divisor group of a Riemann surface — finite formal `ℤ`-linear
combinations of points. Modeled as the finitely supported integer-valued
functions `X →₀ ℤ`. -/

namespace JacobianChallenge.Blueprint

/-- The divisor group of `X`: finite formal integer combinations of
points of `X`. Concretely the type of finitely supported integer-valued
functions on `X`. -/
abbrev Divisor (X : Type*) : Type _ := X →₀ ℤ

end JacobianChallenge.Blueprint
