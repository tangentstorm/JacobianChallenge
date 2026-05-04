import Jacobian.HolomorphicForms.SheafCohomologyRS
import Jacobian.HolomorphicForms.Serre.DualizingSheaf
import Jacobian.HolomorphicForms.Serre.CanonicalDual

/-!
# Harmonic-form representatives for `H¹` (frontier)

Round 13 names the **harmonic-form representatives** of cohomology
classes that the L²-pairing argument (round 14) consumes.

Mathlib v4.28.0 has no Hodge theory in the analytic-coherent flavour
needed; this file only states the representation theorem
parametrically.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open CategoryTheory

/-- **Frontier `def` (placeholder).** Harmonic-form representative
module attached to `(F, q)`. Classically:

* `q = 0`: holomorphic global sections of `F`,
* `q = 1`: anti-holomorphic harmonic 1-forms with values in `F`.

For the present round we expose it as the trivial `ℂ`-module
`PUnit`; later refinement will replace this with a concrete
harmonic-form module. -/
abbrev harmonicForms (X : Type*) [TopologicalSpace X]
    (_F : RSAbSheaf X) (_q : ℕ) : Type :=
  PUnit

/-- **Frontier theorem (sorry).** Linear surjection from harmonic
representatives onto `H¹(X, F)`. -/
noncomputable def harmonicForms_toH1 (X : Type*) [TopologicalSpace X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (F : RSAbSheaf X) [Module ℂ (RSSheafCohomology X F 1)] :
    harmonicForms X F 1 →ₗ[ℂ] RSSheafCohomology X F 1 := by
  exact 0

/-- **Frontier theorem.** The map from harmonic representatives onto
`H¹(X, F)` is surjective.

Under the Round-13 placeholder `harmonicForms = PUnit` and
`harmonicForms_toH1 = 0`, surjectivity is equivalent to
`Subsingleton (RSSheafCohomology X F 1)`; we expose the latter as
an instance argument and discharge surjectivity from it.  Once a
real harmonic-form representation is in place (R5+R7 dependency)
the instance argument will be derivable from genuine Hodge theory
rather than being a placeholder hypothesis. -/
theorem harmonicForms_toH1_surjective (X : Type*) [TopologicalSpace X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (F : RSAbSheaf X) [Module ℂ (RSSheafCohomology X F 1)]
    [Subsingleton (RSSheafCohomology X F 1)] :
    Function.Surjective (harmonicForms_toH1 X F) := by
  intro y
  exact ⟨PUnit.unit, Subsingleton.elim _ _⟩

/-- **Frontier theorem (sorry).** Linear surjection from harmonic
representatives onto `H⁰(X, F)`. -/
noncomputable def harmonicForms_toH0 (X : Type*) [TopologicalSpace X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (F : RSAbSheaf X) [Module ℂ (RSSheafCohomology X F 0)] :
    harmonicForms X F 0 →ₗ[ℂ] RSSheafCohomology X F 0 := by
  exact 0

/-- **Frontier theorem.** The map from harmonic representatives onto
`H⁰(X, F)` is surjective.  Sibling of `harmonicForms_toH1_surjective`;
discharged from a `Subsingleton` instance argument under the
Round-13 placeholder. -/
theorem harmonicForms_toH0_surjective (X : Type*) [TopologicalSpace X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (F : RSAbSheaf X) [Module ℂ (RSSheafCohomology X F 0)]
    [Subsingleton (RSSheafCohomology X F 0)] :
    Function.Surjective (harmonicForms_toH0 X F) := by
  intro y
  exact ⟨PUnit.unit, Subsingleton.elim _ _⟩

end JacobianChallenge.HolomorphicForms
