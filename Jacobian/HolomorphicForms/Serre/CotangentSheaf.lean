import Jacobian.HolomorphicForms.Serre.StructureSheaf
import Jacobian.HolomorphicForms.Serre.CotangentPresheaf

/-!
# Analytic cotangent sheaf `Ω¹_X` (refined)

Round 7 refinement: `RSCotangentSheaf` now assembles the cotangent
presheaf and its sheaf-condition witness from
`Serre/CotangentPresheaf.lean`. This eliminates the round-1 frontier
sorry on `RSCotangentSheaf` itself in favour of two strictly smaller
named obligations (`holomorphicOneFormPresheaf` and
`holomorphicOneFormPresheaf_isSheaf`).

For a 1-dimensional complex manifold (i.e. a Riemann surface) the
cotangent sheaf is the **dualizing sheaf** `K_X`. Round 1 already
arranged `RSDualizingSheaf X := RSCotangentSheaf X` in
`Jacobian/HolomorphicForms/Serre/DualizingSheaf.lean`.

## Refinement role

Round 1: `RSDualizingSheaf X := RSCotangentSheaf X`.
Round 7: `RSCotangentSheaf X := ⟨presheaf, isSheaf⟩`.
-/

namespace JacobianChallenge.HolomorphicForms

open CategoryTheory

/-- **Refined (round 7).** The analytic cotangent sheaf `Ω¹_X` of a
complex-manifold-flavoured topological space `X`, assembled from the
presheaf of holomorphic 1-forms (`holomorphicOneFormPresheaf`,
frontier) and its sheaf-condition witness
(`holomorphicOneFormPresheaf_isSheaf`, frontier). -/
noncomputable def RSCotangentSheaf (X : Type*) [TopologicalSpace X] :
    RSAbSheaf X :=
  ⟨holomorphicOneFormPresheaf X, holomorphicOneFormPresheaf_isSheaf X⟩

end JacobianChallenge.HolomorphicForms
