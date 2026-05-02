import Jacobian.HolomorphicForms.SheafCohomologyRS

/-!
# Cotangent presheaf of holomorphic 1-forms (frontier)

The presheaf `U ↦ Γ(U, Ω¹_X) = { ω | ω is a holomorphic 1-form on U }`
on a complex-manifold-flavoured space, expressed as an
abelian-group-valued presheaf in the form needed by Mathlib's
`TopCat.Presheaf` API.

Round 7 splits the round-1 frontier `RSCotangentSheaf` into:

1. `holomorphicOneFormPresheaf X` — the presheaf (frontier),
2. `holomorphicOneFormPresheaf_isSheaf X` — the sheaf condition
   (frontier),
3. `RSCotangentSheaf X` — the assembled sheaf, sorry-free above
   (1) and (2).
-/

namespace JacobianChallenge.HolomorphicForms

open CategoryTheory

/-- **Frontier `def` (sorry).** Presheaf of holomorphic 1-forms on
`X`, valued in `AddCommGrpCat.{0}`. Classically the section
`Γ(U, Ω¹_X)` is `{ ω : U → T*X | ω is a holomorphic section of T*X }`;
the abelian-group structure is pointwise addition.

This is the round-7 sub-leaf of `RSCotangentSheaf`. -/
noncomputable def holomorphicOneFormPresheaf
    (X : Type*) [TopologicalSpace X] :
    TopCat.Presheaf AddCommGrpCat.{0} (TopCat.of X) := by
  sorry

/-- **Frontier theorem (sorry).** The presheaf
`holomorphicOneFormPresheaf` is a sheaf: holomorphic 1-forms glue
along open covers. -/
theorem holomorphicOneFormPresheaf_isSheaf
    (X : Type*) [TopologicalSpace X] :
    TopCat.Presheaf.IsSheaf (holomorphicOneFormPresheaf X) := by
  sorry

end JacobianChallenge.HolomorphicForms
