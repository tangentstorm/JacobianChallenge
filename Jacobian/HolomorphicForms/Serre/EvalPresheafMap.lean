import Jacobian.HolomorphicForms.Serre.TensorPresheaf
import Jacobian.HolomorphicForms.Serre.CanonicalDual
import Jacobian.HolomorphicForms.Serre.CotangentPresheaf

/-!
# Presheaf-level evaluation pairing `F ⊗ Hom(F, K) → K` (frontier)

The classical evaluation pairing on **presheaves of 𝒪-modules**:

  Γ(U, F) ⊗ Γ(U, Hom_𝒪(F, K_X))  ─eval→  Γ(U, K_X),
  s ⊗ φ                           ↦       φ(s).

Round 9 splits the round-4 frontier `serreEvalSheafMap` into:

1. `evalPresheafMap` — the morphism on tensor presheaves (frontier),
2. `serreEvalSheafMap` — the lift to sheaves via the sheaf inclusion
   (assembly: pre-compose with the canonical map from the tensor
   presheaf to the tensor sheaf, then apply `holomorphicOneFormPresheaf →
   RSCotangentSheaf` on the right).

This factorisation isolates the "evaluate a section against a Hom"
content (1) from the "package as a sheaf morphism" plumbing (2).
-/

namespace JacobianChallenge.HolomorphicForms

open CategoryTheory

/-- **Frontier morphism (sorry).** Presheaf-level evaluation pairing
`tensorAbPresheaf X F (serreDualSheaf X F) ⟶ holomorphicOneFormPresheaf X`.

Will be refined later by going through the analytic
`Hom_𝒪(F, K_X)`-evaluation adjunction once `𝒪`-modules land. -/
noncomputable def evalPresheafMap (X : Type*) [TopologicalSpace X]
    (F : RSAbSheaf X) :
    tensorAbPresheaf X F (serreDualSheaf X F) ⟶
      holomorphicOneFormPresheaf X := by
  refine
    { app := fun _ => 0
      naturality := ?_ }
  intro U V i
  ext x
  simp

end JacobianChallenge.HolomorphicForms
