import Jacobian.HolomorphicForms.SheafCohomologyRS
import Jacobian.HolomorphicForms.Serre.DualizingSheaf
import Jacobian.HolomorphicForms.Defs

/-!
# Identification `H⁰(X, K_X) ≃ HolomorphicOneForm X` (frontier)

Round 23: identify the project-level `HolomorphicOneForm X` (analytic
sections of the cotangent bundle) with `H⁰(X, K_X)` (global sections
of the dualizing sheaf).

Classically these agree definitionally: a global section of the
sheaf of holomorphic 1-forms is exactly an `MDifferentiable` section
of the cotangent bundle. The named obligation here is the bridging
linear equivalence; it is a frontier sorry pending the analytic
structure on `holomorphicOneFormPresheaf`.

Combined with Mathlib's existing
`compactRiemannSurface_finiteDimensionalHolomorphicOneForms`, this
discharges `dim_ℂ H⁰(X, K_X) < ∞` and connects to `analyticGenus X`.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open CategoryTheory

/-- **Frontier `def` (sorry).** Linear equivalence
`H⁰(X, K_X) ≃ₗ[ℂ] HolomorphicOneForm ℂ X`. -/
noncomputable def h0Canonical_isoHolomorphicOneForm
    (X : Type*) [TopologicalSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    [Module ℂ (RSSheafCohomology X (RSDualizingSheaf X) 0)] :
    RSSheafCohomology X (RSDualizingSheaf X) 0 ≃ₗ[ℂ] HolomorphicOneForm ℂ X :=
  sorry

end JacobianChallenge.HolomorphicForms
