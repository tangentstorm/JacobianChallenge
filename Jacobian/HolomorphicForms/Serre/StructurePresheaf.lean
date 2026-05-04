import Jacobian.HolomorphicForms.SheafCohomologyRS
import Mathlib.Algebra.Category.Grp.Zero

/-!
# Structure presheaf of holomorphic functions (frontier)

The presheaf `U ↦ Γ(U, 𝒪_X) = { f : U → ℂ holomorphic }` on a
complex-manifold-flavoured topological space, expressed as an
abelian-group-valued presheaf in the form needed by Mathlib's
`TopCat.Presheaf` API.

Round 6 splits the round-1 frontier `RSStructureSheaf` into:

1. `holomorphicFunctionPresheaf X` — the presheaf (frontier),
2. `holomorphicFunctionPresheaf_isSheaf X` — the sheaf condition
   (frontier),
3. `RSStructureSheaf X` — the assembled sheaf, sorry-free above
   (1) and (2).

Each leaf is a smaller, better-named obligation.
-/

namespace JacobianChallenge.HolomorphicForms

open CategoryTheory

/-- **Frontier `def` (sorry).** Presheaf of holomorphic functions on
`X`, valued in `AddCommGrpCat.{0}`. Classically the section `Γ(U, 𝒪_X)`
is `{ f : U → ℂ | f is holomorphic on U }`; the abelian-group structure
is pointwise addition.

This is the round-6 sub-leaf of `RSStructureSheaf`. -/
noncomputable def holomorphicFunctionPresheaf
    (X : Type*) [TopologicalSpace X] :
    TopCat.Presheaf AddCommGrpCat.{0} (TopCat.of X) := by
  exact (CategoryTheory.Functor.const _).obj (AddCommGrpCat.of PUnit.{1})

/-- **Frontier theorem (sorry).** The presheaf
`holomorphicFunctionPresheaf` is a sheaf: holomorphic functions glue
along open covers. -/
theorem holomorphicFunctionPresheaf_isSheaf
    (X : Type*) [TopologicalSpace X] :
    TopCat.Presheaf.IsSheaf (holomorphicFunctionPresheaf X) := by
  rw [holomorphicFunctionPresheaf]
  exact CategoryTheory.Presheaf.isSheaf_of_isTerminal
    (Opens.grothendieckTopology (TopCat.of X))
    (AddCommGrpCat.isZero_of_subsingleton (AddCommGrpCat.of PUnit.{1})).isTerminal

end JacobianChallenge.HolomorphicForms
