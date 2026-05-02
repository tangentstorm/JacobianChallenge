import Jacobian.HolomorphicForms.Serre.Dolbeault
import Jacobian.HolomorphicForms.Serre.Pairing

/-!
# Hodge / L² nondegeneracy of the Serre pairing (frontier)

Round 11/12 reduce nondegeneracy of `serrePairing` to the witness
form `serrePairing_witness_{left,right}` from `Serre/Dolbeault.lean`.
Round 14 will further refine the witness statements via the L²
inner product on harmonic forms.

This file is intentionally short — it exposes the cleanly-named
"specialised witness for the Serre pairing" obligations that
round 11/12's nondegeneracy proofs cite directly.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open CategoryTheory

/-- **Refined (round 11 -> 14 stub).** Specialised left-witness for
`serrePairing` itself. Body delegates to `serrePairing_witness_left`
applied to `serrePairing X F`. -/
theorem serrePairing_specialised_witness_left
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (F : RSAbSheaf X) :
    letI := serreDualSheaf_module_H0 X F
    letI := serreDualSheaf_module_H1 X F
    ∀ (a : RSSheafCohomology X F 0), a ≠ 0 →
      ∃ b : RSSheafCohomology X (serreDualSheaf X F) 1,
        serrePairing X F a b ≠ 0 := by
  intro a ha
  letI := serreDualSheaf_module_H0 X F
  letI := serreDualSheaf_module_H1 X F
  exact serrePairing_witness_left X F (serrePairing X F) a ha

/-- **Refined (round 12 -> 14 stub).** Specialised right-witness for
`serrePairing` itself. -/
theorem serrePairing_specialised_witness_right
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (F : RSAbSheaf X) :
    letI := serreDualSheaf_module_H0 X F
    letI := serreDualSheaf_module_H1 X F
    ∀ (b : RSSheafCohomology X (serreDualSheaf X F) 1), b ≠ 0 →
      ∃ a : RSSheafCohomology X F 0, serrePairing X F a b ≠ 0 := by
  intro b hb
  letI := serreDualSheaf_module_H0 X F
  letI := serreDualSheaf_module_H1 X F
  exact serrePairing_witness_right X F (serrePairing X F) b hb

end JacobianChallenge.HolomorphicForms
