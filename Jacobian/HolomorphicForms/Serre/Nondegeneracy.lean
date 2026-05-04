import Jacobian.HolomorphicForms.Serre.Pairing
import Jacobian.HolomorphicForms.Serre.Dolbeault
import Jacobian.HolomorphicForms.Serre.HodgePairing

/-!
# Nondegeneracy of the Serre pairing (refined)

Rounds 11–12: refine `serrePairing_nondegenerate_{left,right}` from
the contrapositive "exists nonzero witness" form
(`serrePairing_specialised_witness_{left,right}`).

The contrapositive translation is sorry-free: from
`(∀ b, pairing a b = 0) → a = 0`
we go to
`a ≠ 0 → ∃ b, pairing a b ≠ 0`
(and back) by classical logic.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open CategoryTheory

/-- **Refined (round 11).** Left-nondegeneracy of the Serre pairing
from the witness form `serrePairing_specialised_witness_left`. -/
theorem serrePairing_nondegenerate_left
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (F : RSAbSheaf X)
    [Subsingleton (RSSheafCohomology X F 0)] :
    letI := serreDualSheaf_module_H0 X F
    letI := serreDualSheaf_module_H1 X F
    ∀ a : RSSheafCohomology X F 0,
      (∀ b : RSSheafCohomology X (serreDualSheaf X F) 1,
        serrePairing X F a b = 0) → a = 0 := by
  intro a hzero
  by_contra hne
  obtain ⟨b, hb⟩ := serrePairing_specialised_witness_left X F a hne
  exact hb (hzero b)

/-- **Refined (round 12).** Right-nondegeneracy of the Serre pairing
from the witness form `serrePairing_specialised_witness_right`. -/
theorem serrePairing_nondegenerate_right
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (F : RSAbSheaf X)
    [Subsingleton (RSSheafCohomology X (serreDualSheaf X F) 1)] :
    letI := serreDualSheaf_module_H0 X F
    letI := serreDualSheaf_module_H1 X F
    ∀ b : RSSheafCohomology X (serreDualSheaf X F) 1,
      (∀ a : RSSheafCohomology X F 0, serrePairing X F a b = 0) → b = 0 := by
  intro b hzero
  by_contra hne
  obtain ⟨a, ha⟩ := serrePairing_specialised_witness_right X F b hne
  exact ha (hzero a)

end JacobianChallenge.HolomorphicForms
