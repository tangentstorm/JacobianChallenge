import Jacobian.HolomorphicForms.SheafCohomologyRS
import Jacobian.HolomorphicForms.Serre.TensorPresheaf

/-!
# Tensor product of abelian sheaves over the structure sheaf (refined)

Round 8 refinement: `RSTensorAbSheaf X F G` is now assembled from the
tensor presheaf and its sheaf-condition witness, replacing the
round-4 single sorry by two strictly smaller named obligations
(`tensorAbPresheaf` and `tensorAbPresheaf_isSheaf`).

For the Serre-pairing route we only need this for the case
`G = serreDualSheaf F`; the `def` is stated more generally so the
cup product API in round 10 can hand it any pair of sheaves.
-/

namespace JacobianChallenge.HolomorphicForms

open CategoryTheory

/-- **Refined (round 8).** Tensor product `F ⊗_𝒪 G` of two abelian
sheaves on `X`, assembled from the tensor presheaf
(`tensorAbPresheaf`, frontier) and its sheaf-condition witness
(`tensorAbPresheaf_isSheaf`, frontier). -/
noncomputable def RSTensorAbSheaf (X : Type*) [TopologicalSpace X]
    (F G : RSAbSheaf X) : RSAbSheaf X :=
  ⟨tensorAbPresheaf X F G, tensorAbPresheaf_isSheaf X F G⟩

end JacobianChallenge.HolomorphicForms
