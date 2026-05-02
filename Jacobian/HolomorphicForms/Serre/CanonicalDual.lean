import Jacobian.HolomorphicForms.Serre.CotangentSheaf

/-!
# Canonical Serre dual `Hom_𝒪(F, K_X)` (frontier)

Project-side frontier `def` for the **canonical dual sheaf** that
appears on the right of Serre duality:

  Fᵛ_K := Hom_𝒪(F, K_X)

(equivalently, for locally-free `F`, the underlying-sheaf of
`F^∨ ⊗ K_X`). Round 2 of the Serre-duality top-down refinement uses
this declaration as the canonical witness for the existential
`dualSheaf` produced by `serre_duality_rs`.

The two `Module ℂ` instances declared here record the
`ℂ`-vector-space structure on `H⁰(X, F)` and `H¹(X, serreDualSheaf F)`
that `SerreDualityRSDatum` requires; they are frontier sorries
because the abelian-group structure on `Sheaf.H` does not auto-promote
to a `ℂ`-module structure without analytic-sheaf machinery.

## Mathlib v4.28.0 status

ABSENT — internal Hom and tensor for analytic `𝒪_X`-modules are not
in Mathlib v4.28.0.

## Refinement role

* Round 2 (this file) introduces `serreDualSheaf`,
  `serreDualSheaf_module_H0`, `serreDualSheaf_module_H1`.
* Round 3 will introduce `serre_datum_for_canonical_dual` (a
  `Nonempty` of the abstract datum).
* `serre_duality_rs` then reduces to assembling these named
  obligations.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open CategoryTheory

/-- **Frontier `def` (sorry).** The canonical Serre-dual sheaf
`Hom_𝒪(F, K_X)` of an abelian sheaf `F` on a complex-manifold-flavoured
space `X`, viewed as an abelian sheaf via the project's `RSAbSheaf`
alias.

Will be refined later via the internal-Hom + tensor-product machinery
of `𝒪_X`-modules (rounds 8–9). -/
noncomputable def serreDualSheaf (X : Type*) [TopologicalSpace X]
    (_F : RSAbSheaf X) : RSAbSheaf X :=
  sorry

/-- **Frontier instance (sorry).** The `ℂ`-module structure on
`H⁰(X, F)` required by `SerreDualityRSDatum`. Mathlib's `Sheaf.H`
provides only an `AddCommGroup`; the `ℂ`-action would come from a
sheaf-of-`ℂ`-vector-spaces (or `𝒪_X`-module) realisation of `F`,
which is ABSENT in v4.28.0. -/
noncomputable def serreDualSheaf_module_H0
    (X : Type*) [TopologicalSpace X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (F : RSAbSheaf X) :
    Module ℂ (RSSheafCohomology X F 0) :=
  sorry

/-- **Frontier instance (sorry).** The `ℂ`-module structure on
`H¹(X, Hom(F, K_X))` required by `SerreDualityRSDatum`. -/
noncomputable def serreDualSheaf_module_H1
    (X : Type*) [TopologicalSpace X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (F : RSAbSheaf X) :
    Module ℂ (RSSheafCohomology X (serreDualSheaf X F) 1) :=
  sorry

end JacobianChallenge.HolomorphicForms
