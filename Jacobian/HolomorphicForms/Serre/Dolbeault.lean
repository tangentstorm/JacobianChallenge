import Jacobian.HolomorphicForms.SheafCohomologyRS
import Jacobian.HolomorphicForms.Serre.DualizingSheaf
import Jacobian.HolomorphicForms.Serre.CanonicalDual
import Jacobian.HolomorphicForms.Serre.HarmonicForms
import Jacobian.HolomorphicForms.Serre.L2Pairing

/-!
# Dolbeault identification of `H¹` (frontier)

On a compact Riemann surface, the Dolbeault theorem identifies

  H¹(X, F) ≃ HarmonicForms(X, F)

(complex anti-harmonic / `(0,1)`-form representatives), and likewise

  H⁰(X, F) ≃ HolomorphicSections(X, F)
  H¹(X, K_X) ≃ ℂ.

We do NOT formalise the harmonic-forms module here; rounds 13/14 will
refine the Dolbeault identification into named obligations above
named L² and harmonic-form spaces. This round just exposes a simple
*scalar witness pairing*: for any nonzero class in `H⁰(X, F)` there
exists a class in `H¹(X, Hom(F, K_X))` whose Serre-pairing with it is
nonzero. Round 11 reduces the abstract `serrePairing_nondegenerate_left`
to this witness existence.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open CategoryTheory

/-- **Refined (round 13).** "Witness" form of Serre nondegeneracy on
the left, factored through the harmonic-form representative lifts
(`harmonicForms_toH0` + `harmonicForms_toH1`) and the L²-pairing
nondegeneracy (`harmonicL2Pairing_witness_left`). The key
compatibility is `harmonicL2Pairing_compatible`, which relates the
abstract `pairing` to `harmonicL2Pairing` via the lifts. -/
theorem serrePairing_witness_left
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (F : RSAbSheaf X)
    [Module ℂ (RSSheafCohomology X F 0)]
    [Module ℂ (RSSheafCohomology X (serreDualSheaf X F) 1)]
    [Subsingleton (RSSheafCohomology X F 0)]
    (pairing :
      RSSheafCohomology X F 0 →ₗ[ℂ]
        RSSheafCohomology X (serreDualSheaf X F) 1 →ₗ[ℂ] ℂ)
    (a : RSSheafCohomology X F 0) (ha : a ≠ 0) :
    ∃ b : RSSheafCohomology X (serreDualSheaf X F) 1,
      pairing a b ≠ 0 := by
  obtain ⟨α, rfl⟩ := harmonicForms_toH0_surjective X F a
  have hα : harmonicForms_toH0 X F α ≠ 0 := ha
  obtain ⟨β, hβ⟩ := harmonicL2Pairing_witness_left X F α hα
  exact ⟨harmonicForms_toH1 X (serreDualSheaf X F) β,
    by rw [harmonicL2Pairing_compatible X F pairing α β]; exact hβ⟩

/-- **Refined (round 13).** "Witness" form of Serre nondegeneracy on
the right, dual to `serrePairing_witness_left`. -/
theorem serrePairing_witness_right
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (F : RSAbSheaf X)
    [Module ℂ (RSSheafCohomology X F 0)]
    [Module ℂ (RSSheafCohomology X (serreDualSheaf X F) 1)]
    [Subsingleton (RSSheafCohomology X (serreDualSheaf X F) 1)]
    (pairing :
      RSSheafCohomology X F 0 →ₗ[ℂ]
        RSSheafCohomology X (serreDualSheaf X F) 1 →ₗ[ℂ] ℂ)
    (b : RSSheafCohomology X (serreDualSheaf X F) 1) (hb : b ≠ 0) :
    ∃ a : RSSheafCohomology X F 0, pairing a b ≠ 0 := by
  -- Lift b to a harmonic representative β via surjectivity of the
  -- harmonic-form projection onto H¹.
  obtain ⟨β, hβ⟩ := harmonicForms_toH1_surjective X (serreDualSheaf X F) b
  -- The harmonic representative maps to a nonzero cohomology class.
  have hβ_ne : harmonicForms_toH1 X (serreDualSheaf X F) β ≠ 0 := hβ ▸ hb
  -- Apply L²-pairing nondegeneracy on the right to obtain a harmonic
  -- witness α whose L²-pairing with β is nonzero.
  obtain ⟨α, hα⟩ := harmonicL2Pairing_witness_right X F β hβ_ne
  -- Push α down to H⁰ and relate pairings via compatibility.
  exact ⟨harmonicForms_toH0 X F α, by
    rw [← hβ, harmonicL2Pairing_compatible X F pairing α β]
    exact hα⟩

end JacobianChallenge.HolomorphicForms
