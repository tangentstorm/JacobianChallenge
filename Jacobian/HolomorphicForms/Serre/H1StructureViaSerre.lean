import Jacobian.HolomorphicForms.Serre.LineBundleSerre
import Jacobian.HolomorphicForms.Serre.LineBundleDual
import Jacobian.HolomorphicForms.Serre.H0CanonicalIdentification
import Jacobian.HolomorphicForms.Serre.StructureSheaf
import Jacobian.HolomorphicForms.Defs

/-!
# Identification `H¹(X, 𝒪_X) ≃ HolomorphicOneForm X *` (frontier)

Round 24: combining Serre duality `H¹(X, 𝒪_X)* ≃ H⁰(X, K_X)` with
the round-23 identification `H⁰(K_X) ≃ HolomorphicOneForm ℂ X` gives

  H¹(X, 𝒪_X)  ≃  HolomorphicOneForm ℂ X *  (as ℂ-vector spaces).

In particular, `dim_ℂ H¹(X, 𝒪_X) = dim_ℂ HolomorphicOneForm ℂ X = g`,
i.e. the genus.

This is the analytic-side discharge for the dimension equality
`analyticGenus X = dim_ℂ H¹(X, 𝒪_X)` underlying
`Jacobian/HolomorphicForms/GenusEqH0Canonical.lean`.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open CategoryTheory

/-- **Frontier theorem (sorry).** Identification of `H¹(X, 𝒪_X)` with
the dual of `HolomorphicOneForm X`, as ℂ-vector spaces.

The proof goes via Serre duality on `F = 𝒪_X` (whose canonical dual
is `K_X`), combined with `h0Canonical_isoHolomorphicOneForm` (round
23). -/
noncomputable def h1Structure_isoHolomorphicOneFormDual
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSStructureSheaf X) 1)] :
    RSSheafCohomology X (RSStructureSheaf X) 1 ≃ₗ[ℂ]
      Module.Dual ℂ (HolomorphicOneForm ℂ X) :=
  sorry

/-- **Frontier theorem (sorry).** Dimension consequence:
`dim_ℂ H¹(X, 𝒪_X) = dim_ℂ HolomorphicOneForm ℂ X`. -/
theorem h1Structure_finrank_eq_holomorphicOneForm
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSStructureSheaf X) 1)]
    [FiniteDimensional ℂ (HolomorphicOneForm ℂ X)] :
    Module.finrank ℂ (RSSheafCohomology X (RSStructureSheaf X) 1) =
      Module.finrank ℂ (HolomorphicOneForm ℂ X) := by
  rw [LinearEquiv.finrank_eq (h1Structure_isoHolomorphicOneFormDual X)]
  exact Subspace.dual_finrank_eq

end JacobianChallenge.HolomorphicForms
