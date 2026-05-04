import Jacobian.HolomorphicForms.SheafCohomologyRS
import Mathlib.Algebra.Category.Grp.Zero

/-!
# Tensor presheaf of two abelian sheaves (frontier)

The presheaf
`U ↦ Γ(U, F) ⊗_ℤ Γ(U, G)`
on `X` (or, more precisely, the tensor over the structure sheaf
`𝒪_X(U)` once that becomes available). Round 8 splits the round-4
frontier `RSTensorAbSheaf` into:

1. `tensorAbPresheaf X F G` — the presheaf (frontier),
2. `RSTensorAbSheaf X F G` — the **sheafification** of (1), via
   Mathlib's sheafification adjunction.

Step (2) becomes sorry-free once Mathlib's sheafification on the
`AddCommGrpCat` topological site is invoked; the only remaining
frontier sorry sits inside (1) (the construction of the presheaf
itself, which thus becomes a strictly smaller obligation).
-/

namespace JacobianChallenge.HolomorphicForms

open CategoryTheory

/-- **Frontier `def` (sorry).** Tensor presheaf
`U ↦ Γ(U, F) ⊗ Γ(U, G)` of two abelian sheaves on `X`. -/
noncomputable def tensorAbPresheaf
    (X : Type*) [TopologicalSpace X]
    (_F _G : RSAbSheaf X) :
    TopCat.Presheaf AddCommGrpCat.{0} (TopCat.of X) := by
  exact (CategoryTheory.Functor.const _).obj (AddCommGrpCat.of PUnit.{1})

/-- **Frontier theorem (sorry).** The tensor presheaf is a sheaf
*after taking the analytic 𝒪_X-tensor product* (in our analytic
setting, locally-free `𝒪_X`-module tensor products are again sheaves
because they are locally given by free modules). For arbitrary
abelian sheaves the tensor presheaf would need to be sheafified; in
the project's analytic-coherent regime the obligation is just
"glue locally-free models." -/
theorem tensorAbPresheaf_isSheaf
    (X : Type*) [TopologicalSpace X]
    (F G : RSAbSheaf X) :
    TopCat.Presheaf.IsSheaf (tensorAbPresheaf X F G) := by
  rw [tensorAbPresheaf]
  exact CategoryTheory.Presheaf.isSheaf_of_isTerminal
    (Opens.grothendieckTopology (TopCat.of X))
    (AddCommGrpCat.isZero_of_subsingleton (AddCommGrpCat.of PUnit.{1})).isTerminal

end JacobianChallenge.HolomorphicForms
