import Jacobian.HolomorphicForms.SheafCohomologyRS
import Jacobian.Periods.TrivializationContinuousLinearMapAt

/-!
# Serre-duality datum (structure)

The abstract data of Serre duality for a single abelian sheaf `F` on
a compact Riemann surface `X`, against a chosen candidate dual sheaf:
the `ℂ`-bilinear pairing plus left/right nondegeneracy axioms.

Lifted out of `SerreDualityRS.lean` so that the canonical-dual files
under `Serre/` can refine the existence theorem without forming a
circular import. The original public name
`JacobianChallenge.HolomorphicForms.SerreDualityRSDatum` is preserved
because everything is in the same namespace, and `SerreDualityRS.lean`
still re-imports this file.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open CategoryTheory

/-- Serre duality datum for a single abelian sheaf `F` on a compact
Riemann surface `X`, against a fixed candidate dual sheaf `dualSheaf`
(which classically is `Hom_𝒪(F, K_X)` ≃ `F^∨ ⊗ K_X`).

Records the abstract data — pairing and nondegeneracy — needed to
state Riemann-Roch / Serre-pairing-style consequences without
committing to an explicit construction. Once coherent analytic
sheaves land in Mathlib (or via an ad-hoc argument for specific
sheaves), an inhabitant of this structure can be supplied and the
downstream machinery snaps together.

Both nondegeneracy axioms are recorded in the conventional "left/right
radical is trivial" form. -/
structure SerreDualityRSDatum
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (F dualSheaf : RSAbSheaf X)
    [Module ℂ (RSSheafCohomology X F 0)]
    [Module ℂ (RSSheafCohomology X dualSheaf 1)] where
  /-- The Serre pairing `H⁰(X, F) × H¹(X, Fᵛ ⊗ K_X) → ℂ`. -/
  pairing :
    RSSheafCohomology X F 0 →ₗ[ℂ] RSSheafCohomology X dualSheaf 1 →ₗ[ℂ] ℂ
  /-- The pairing is nondegenerate on the left: a class in `H⁰(X, F)`
  pairing trivially with every class in `H¹(X, Fᵛ ⊗ K_X)` is zero. -/
  nondegenerate_left :
    ∀ a : RSSheafCohomology X F 0,
      (∀ b : RSSheafCohomology X dualSheaf 1, pairing a b = 0) → a = 0
  /-- The pairing is nondegenerate on the right: a class in
  `H¹(X, Fᵛ ⊗ K_X)` paired trivially with every class in `H⁰(X, F)`
  is zero. -/
  nondegenerate_right :
    ∀ b : RSSheafCohomology X dualSheaf 1,
      (∀ a : RSSheafCohomology X F 0, pairing a b = 0) → b = 0

end JacobianChallenge.HolomorphicForms
