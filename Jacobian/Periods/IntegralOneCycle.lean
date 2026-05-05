import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Integral 1-cycles via singular homology

Queue D scaffolding. Defines `IntegralOneCycle X` as the underlying
ℤ-module of `H₁(X, ℤ)`, by composing Mathlib's
`singularHomologyFunctor` (`Mathlib/AlgebraicTopology/SingularHomology/Basic.lean`)
with the `ModuleCat ℤ` ambient category.

This is the "1-chains modulo boundaries" definition used by the
period pairing.
-/

namespace JacobianChallenge.Periods

open CategoryTheory

/-- The integral 1-cycles on a topological space `X`: the underlying
ℤ-module of `H₁(X, ℤ)`. Built from Mathlib's `singularHomologyFunctor`
in degree 1, with coefficients in `ModuleCat.of ℤ ℤ`.

Note on universe: explicitly threaded as universe 0 (`X : Type`) because
`singularHomologyFunctor` requires `[HasCoproducts.{w} (ModuleCat ℤ)]`
where `w` matches `X`'s universe, and the available instance for
`ModuleCat ℤ` is at universe 0. Lifting to `(X : Type u)` would require
either an instance of `HasCoproducts.{u} (ModuleCat ℤ)` (which Mathlib
doesn't provide universe-polymorphically out of the box) or a `ULift`
bridge. See `Jacobian/Periods/PathIntegralViaCoverRecon.lean` for
related design discussion. -/
noncomputable def IntegralOneCycle (X : Type) [TopologicalSpace X] :
    ModuleCat ℤ :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) 1).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)

end JacobianChallenge.Periods
