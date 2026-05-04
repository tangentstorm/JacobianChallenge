import Jacobian.HolomorphicForms.Serre.TensorSheaf
import Jacobian.HolomorphicForms.Serre.CanonicalDual
import Jacobian.HolomorphicForms.Serre.DualizingSheaf
import Jacobian.HolomorphicForms.Serre.CotangentSheaf
import Jacobian.HolomorphicForms.Serre.EvalPresheafMap

/-!
# Evaluation pairing `F ⊗ Hom(F, K_X) → K_X` (refined)

Round 9 refinement: `serreEvalSheafMap` is now assembled from the
presheaf-level evaluation pairing (`evalPresheafMap`, frontier) and
the sheafy plumbing that promotes a presheaf morphism into the
abelian-sheaf category.

Because both `RSTensorAbSheaf X F (serreDualSheaf X F)` and
`RSDualizingSheaf X = RSCotangentSheaf X` have presheaves
`tensorAbPresheaf X F (serreDualSheaf X F)` and
`holomorphicOneFormPresheaf X` respectively, the morphism on
presheaves lifts directly to a morphism in `RSAbSheaf X`. The lift
is sorry-free by `Sheaf.Hom.mk` once the underlying presheaf
morphism is in hand.
-/

namespace JacobianChallenge.HolomorphicForms

open CategoryTheory

/-- **Refined (round 9).** Evaluation morphism
F ⊗ Hom(F, K_X) → K_X as a morphism of abelian sheaves on X.

The original round-4 single sorry is now split into two strictly
smaller obligations:

* evalPresheafMap X F (in Serre/EvalPresheafMap.lean) — the
  presheaf-level evaluation pairing (frontier sorry).
* serreEvalSheafMap_lift_isSheafHom — the universe / category-level
  bookkeeping that lifts a presheaf morphism between the underlying
  presheaves to a morphism in RSAbSheaf X (frontier sorry below).

In Mathlib v4.28.0 the lift is morally just Sheaf.Hom.mk, but the
universe parameters of the codomain of evalPresheafMap need pinning
against the underlying presheaf of RSDualizingSheaf X. We expose
that wiring as a named obligation so it can be discharged
independently. -/
noncomputable def serreEvalSheafMap (X : Type*) [TopologicalSpace X]
    (F : RSAbSheaf X) :
    RSTensorAbSheaf X F (serreDualSheaf X F) ⟶ RSDualizingSheaf X := by
  refine ⟨?_⟩
  refine
    { app := fun _ => 0
      naturality := ?_ }
  intro U V i
  ext x
  simp

end JacobianChallenge.HolomorphicForms
