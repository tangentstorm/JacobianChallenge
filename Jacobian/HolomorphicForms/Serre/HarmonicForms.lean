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
  sorry

/-- **Frontier theorem (sorry).** The map from harmonic
representatives onto `H¹(X, F)` is surjective. -/
theorem harmonicForms_toH1_surjective (X : Type*) [TopologicalSpace X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (F : RSAbSheaf X) [Module ℂ (RSSheafCohomology X F 1)] :
    Function.Surjective (harmonicForms_toH1 X F) := by
  sorry

/-- **Frontier theorem (sorry).** Linear surjection from harmonic
representatives onto `H⁰(X, F)`. -/
noncomputable def harmonicForms_toH0 (X : Type*) [TopologicalSpace X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (F : RSAbSheaf X) [Module ℂ (RSSheafCohomology X F 0)] :
    harmonicForms X F 0 →ₗ[ℂ] RSSheafCohomology X F 0 := by
  sorry

/-- **Frontier theorem (sorry).** The map from harmonic
representatives onto `H⁰(X, F)` is surjective. -/
theorem harmonicForms_toH0_surjective (X : Type*) [TopologicalSpace X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (F : RSAbSheaf X) [Module ℂ (RSSheafCohomology X F 0)] :
    Function.Surjective (harmonicForms_toH0 X F) := by
  sorry

end JacobianChallenge.HolomorphicForms
