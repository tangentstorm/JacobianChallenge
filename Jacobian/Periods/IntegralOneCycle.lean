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

universe u

/-- The integral 1-cycles on a topological space `X`: the underlying
ℤ-module of `H₁(X, ULift ℤ)`. Built from Mathlib's
`singularHomologyFunctor` in degree 1, with coefficients in
`ModuleCat.of ℤ (ULift.{u} ℤ)`.

The coefficient ring `ULift.{u} ℤ` (rather than `ℤ` itself) lives in
`Type u`, so `ModuleCat.of ℤ (ULift.{u} ℤ) : ModuleCat.{u} ℤ` matches
the universe of `TopCat.of X : TopCat.{u}` produced from `X : Type u`.
The required `HasCoproducts.{u} (ModuleCat.{u} ℤ)` instance is the
universe-polymorphic chain in
`Mathlib/Algebra/Category/Grp/Colimits.lean:270` +
`Mathlib/Algebra/Category/ModuleCat/Colimits.lean:115` (already in
v4.28.0; see `ref/plans/mathlib-hascoproducts-report.org`).

`ULift.{u} ℤ` and `ℤ` are canonically `AddCommGroup`-isomorphic, so
the resulting ℤ-module `IntegralOneCycle X` is the singular `H₁`
group up to canonical isomorphism. -/
noncomputable def IntegralOneCycle (X : Type u) [TopologicalSpace X] :
    ModuleCat.{u} ℤ :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) 1).obj
    (ModuleCat.of ℤ (ULift.{u} ℤ))).obj (TopCat.of X)

end JacobianChallenge.Periods
