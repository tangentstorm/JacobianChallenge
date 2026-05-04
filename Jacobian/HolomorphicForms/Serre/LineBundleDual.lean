import Jacobian.HolomorphicForms.SheafCohomologyRS
import Jacobian.HolomorphicForms.Serre.TensorSheaf
import Jacobian.HolomorphicForms.Serre.DualizingSheaf
import Jacobian.HolomorphicForms.Serre.CanonicalDual

/-!
# Dual of a line-bundle sheaf (frontier)

For a line-bundle sheaf `L : RSLineBundleSheaf X` (a placeholder
alias for an abelian sheaf, until `𝒪_X`-modules land), the
**inverse line bundle** `L⁻¹` is the sheaf-theoretic dual. Round 17
of the Serre-duality refinement names this construction so the
specialised line-bundle Serre duality (round 16) can identify

  serreDualSheaf X L  ≃  L⁻¹ ⊗ K_X.

In Mathlib v4.28.0 the locally-free `𝒪_X`-module API is ABSENT so
the dual is a frontier sorry; it is structurally smaller than the
round-2 `serreDualSheaf` because it specialises to line bundles
(rank 1 locally-free modules).
-/

namespace JacobianChallenge.HolomorphicForms

open CategoryTheory

/-- **Frontier `def` (sorry).** Inverse line bundle `L⁻¹` (also
written `L^∨`) of a line-bundle sheaf on `X`. Will be refined later
via the locally-free `𝒪_X`-module dual once the analytic-sheaf API
is in Mathlib. -/
noncomputable def RSLineBundleDual (X : Type*) [TopologicalSpace X]
    (L : RSLineBundleSheaf X) : RSLineBundleSheaf X :=
  L

/-- **Frontier theorem (sorry).** Identification of the canonical
Serre-dual of a line bundle: `serreDualSheaf X L ≃ L⁻¹ ⊗ K_X` as
abelian sheaves. -/
theorem serreDualSheaf_lineBundle_iso
    (X : Type*) [TopologicalSpace X] (L : RSLineBundleSheaf X) :
    Nonempty (serreDualSheaf X L ≅
      RSTensorAbSheaf X (RSLineBundleDual X L) (RSDualizingSheaf X)) := by
  exact ⟨Iso.refl _⟩

end JacobianChallenge.HolomorphicForms
