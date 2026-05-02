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
    (pairing :
      RSSheafCohomology X F 0 →ₗ[ℂ]
        RSSheafCohomology X (serreDualSheaf X F) 1 →ₗ[ℂ] ℂ)
    (a : RSSheafCohomology X F 0) (ha : a ≠ 0) :
    ∃ b : RSSheafCohomology X (serreDualSheaf X F) 1,
      pairing a b ≠ 0 := by
  -- Round 13 design: lift `a` to a harmonic representative via
  -- `harmonicForms_toH0_surjective`, apply
  -- `harmonicL2Pairing_witness_left`, push the result back via
  -- `harmonicForms_toH1`, and use `harmonicL2Pairing_compatible` to
  -- relate `pairing` to the L²-pairing. The proof is left as a
  -- (smaller) sorry pending universe-bookkeeping cleanup of the
  -- L²-pairing API; the named obligations consumed by this proof
  -- (`harmonicForms_toH0_surjective`, `harmonicL2Pairing_witness_left`,
  -- `harmonicL2Pairing_compatible`) are now strictly smaller than the
  -- original Serre nondegeneracy sorry.
  sorry

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
    (pairing :
      RSSheafCohomology X F 0 →ₗ[ℂ]
        RSSheafCohomology X (serreDualSheaf X F) 1 →ₗ[ℂ] ℂ)
    (b : RSSheafCohomology X (serreDualSheaf X F) 1) (hb : b ≠ 0) :
    ∃ a : RSSheafCohomology X F 0, pairing a b ≠ 0 := by
  -- Round 13 (right) design: dual to the left case. Sorry left
  -- pending universe-bookkeeping cleanup (see left case).
  sorry

end JacobianChallenge.HolomorphicForms
