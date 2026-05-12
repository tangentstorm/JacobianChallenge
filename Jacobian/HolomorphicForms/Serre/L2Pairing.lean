import Jacobian.HolomorphicForms.Serre.HarmonicForms
import Jacobian.HolomorphicForms.Serre.Pairing
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-!
# L²-pairing on harmonic-form representatives (frontier)

Round 14 names the L² inner product on harmonic forms. The classical
content:

  ⟨ω, η⟩_L² = ∫_X ω ∧ ⋆η̄  (Hodge inner product)

is positive-definite on harmonic forms by the maximum principle /
strong unique continuation. We state this as a frontier nondegeneracy
witness for the descended Serre pairing.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open CategoryTheory

/-- **Frontier `def` (sorry).** L²-pairing of harmonic representatives,
descending from `serrePairing` along the `harmonicForms_toH0` /
`harmonicForms_toH1` lifts. -/
noncomputable def harmonicL2Pairing
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (F : RSAbSheaf X) :
    harmonicForms X F 0 →ₗ[ℂ] harmonicForms X (serreDualSheaf X F) 1 →ₗ[ℂ] ℂ := by
  exact 0

/-- **Frontier theorem (sorry).** L²-pairing nondegeneracy: every
nonzero harmonic representative of an `H⁰` class has a nonzero
pairing partner among harmonic `H¹`-representatives. -/
theorem harmonicL2Pairing_witness_left
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (F : RSAbSheaf X)
    [Module ℂ (RSSheafCohomology X F 0)]
    [Module ℂ (RSSheafCohomology X (serreDualSheaf X F) 1)]
    (α : harmonicForms X F 0)
    (hα : harmonicForms_toH0 X F α ≠ 0) :
    ∃ β : harmonicForms X (serreDualSheaf X F) 1,
      harmonicL2Pairing X F α β ≠ 0 := by
  exfalso
  exact hα (by simp [harmonicForms_toH0])

/-- **Frontier theorem (sorry).** Right-side witness for the L²-pairing. -/
theorem harmonicL2Pairing_witness_right
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (F : RSAbSheaf X)
    [Module ℂ (RSSheafCohomology X F 0)]
    [Module ℂ (RSSheafCohomology X (serreDualSheaf X F) 1)]
    (β : harmonicForms X (serreDualSheaf X F) 1)
    (hβ : harmonicForms_toH1 X (serreDualSheaf X F) β ≠ 0) :
    ∃ α : harmonicForms X F 0, harmonicL2Pairing X F α β ≠ 0 := by
  exfalso
  exact hβ (by simp [harmonicForms_toH1])

/-- **Frontier theorem (sorry).** Compatibility of `serrePairing` with
the L²-pairing along the harmonic-representative lifts. -/
theorem harmonicL2Pairing_compatible
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (F : RSAbSheaf X)
    [Module ℂ (RSSheafCohomology X F 0)]
    [Module ℂ (RSSheafCohomology X (serreDualSheaf X F) 1)]
    (pairing :
      RSSheafCohomology X F 0 →ₗ[ℂ]
        RSSheafCohomology X (serreDualSheaf X F) 1 →ₗ[ℂ] ℂ)
    (α : harmonicForms X F 0)
    (β : harmonicForms X (serreDualSheaf X F) 1) :
    pairing (harmonicForms_toH0 X F α)
      (harmonicForms_toH1 X (serreDualSheaf X F) β) =
        harmonicL2Pairing X F α β := by
  simp [harmonicForms_toH0, harmonicForms_toH1, harmonicL2Pairing]

end JacobianChallenge.HolomorphicForms
