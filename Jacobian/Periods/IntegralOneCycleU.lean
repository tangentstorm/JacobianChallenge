import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Jacobian.Periods.IntegralOneCycle

/-!
# Universe-polymorphic integral 1-cycles

`Jacobian/Periods/IntegralOneCycle.lean` defines `IntegralOneCycle (X : Type)`
at universe 0, because its many downstream consumers (the cellular-homology
rank lemmas in `IntegralOneCycleRank.lean` / `CellularHomologyRS.lean`, the
de-Rham comparison in `HolomorphicForms/DeRhamComparisonMap.lean`, the
`singularH1` re-exposure in `TopologicalGenus.lean`, …) all pin the singular
homology functor to coefficients `ModuleCat.of ℤ ℤ` in `ModuleCat.{0} ℤ` and
rely on that exact coefficient identity. Widening that definition in place
breaks all of them.

This file adds a **separate**, universe-polymorphic homology object
`IntegralOneCycleU (X : Type u)` living in `ModuleCat.{u} ℤ`, obtained by
instantiating Mathlib's `singularHomologyFunctor` at universe `u` with
coefficients `ULift.{u} ℤ`. The `ULift.{u} ℤ` coefficient is forced: the
functor `singularHomologyFunctor.{u}` demands its coefficient category be a
`Category.{u}`, so `ModuleCat.{u} ℤ` (whose objects are `ℤ`-modules in
`Type u`) is the only choice, and `ULift.{u} ℤ` is the `Type u` copy of the
coefficient module `ℤ`.

The public universe-polymorphic Jacobian bridge (`Jacobian/Solution.lean`)
routes the period pairing through this object, so that
`periodFullComplexLattice` — and hence `Jacobian (X : Type u)` — type-checks
for an arbitrary `X : Type u`, while the `Type 0` homology subsystem above is
left completely untouched.

For `X : Type 0` this is *not* definitionally equal to `IntegralOneCycle X`
(the coefficient module differs: `ULift.{0} ℤ` vs `ℤ`), but it is canonically
isomorphic; the period subgroup it produces in `Fin (genus X) → ℂ` agrees,
which is all the downstream lattice machinery observes.
-/

namespace JacobianChallenge.Periods

open CategoryTheory

universe u

/--
The integral 1-cycles on a topological space `X : Type u`: the underlying
ℤ-module of `H₁(X, ℤ)`, as an object of `ModuleCat.{u} ℤ`.

Universe-polymorphic companion to `IntegralOneCycle` (which is pinned to
`Type 0`); see the module docstring for why the two cannot be merged.
-/
noncomputable def IntegralOneCycleU (X : Type u) [TopologicalSpace X] :
    ModuleCat.{u} ℤ :=
  ((AlgebraicTopology.singularHomologyFunctor.{u} (ModuleCat.{u} ℤ) 1).obj
    (ModuleCat.of ℤ (ULift.{u} ℤ))).obj (TopCat.of X)

/--
**Provider (Universe-`u` Homology Functoriality).**
A homeomorphism between spaces in `Type u` induces a `LinearEquiv` on `IntegralOneCycleU`.

This is a tracked layer-frontier sorry. Its discharge requires transporting
`singularH1_iso_of_homotopyEquiv_via_prism` to `Type u` or directly using the
Mathlib singular homology functoriality.
-/
theorem IntegralOneCycleULinearEquivOfHomeo {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y) :
    Nonempty (IntegralOneCycleU X ≃ₗ[ℤ] IntegralOneCycleU Y) := by
  let F := (AlgebraicTopology.singularHomologyFunctor.{u} (ModuleCat.{u} ℤ) 1).obj (ModuleCat.of ℤ (ULift.{u} ℤ))
  have isoTop : TopCat.of X ≅ TopCat.of Y := TopCat.isoOfHomeo h
  have isoMod : F.obj (TopCat.of X) ≅ F.obj (TopCat.of Y) := Functor.mapIso F isoTop
  exact ⟨isoMod.toLinearEquiv⟩

end JacobianChallenge.Periods
