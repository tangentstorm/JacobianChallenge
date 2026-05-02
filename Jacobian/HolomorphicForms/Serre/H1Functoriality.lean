import Jacobian.HolomorphicForms.SheafCohomologyRS

/-!
# Functoriality of `H¹` along sheaf morphisms (frontier)

A morphism of abelian sheaves `φ : F ⟶ G` induces a `ℂ`-linear map
`H¹(X, F) → H¹(X, G)`. Mathlib's `Sheaf.H` is functorial in the sheaf
argument as an `AddCommGroup`-map; the `ℂ`-linear refinement requires
that both sides carry compatible `Module ℂ` structures, which is
what the project-level `Module` instance arguments provide.

This frontier file packages the linear map that round 4 needs to
compose `cup ∘ eval ∘ trace`. It is itself frontier-sorry because the
`ℂ`-action compatibility with arbitrary sheaf-level maps in the
abelian-sheaf model is not auto-derivable.
-/

namespace JacobianChallenge.HolomorphicForms

open CategoryTheory

/-- **Frontier `def` (sorry).** `ℂ`-linear map on `H¹` induced by a
morphism of abelian sheaves, given the `ℂ`-module structures on both
sides. -/
noncomputable def serreH1Map
    (X : Type*) [TopologicalSpace X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    {F G : RSAbSheaf X} (_φ : F ⟶ G)
    [_mF : Module ℂ (RSSheafCohomology X F 1)]
    [_mG : Module ℂ (RSSheafCohomology X G 1)] :
    RSSheafCohomology X F 1 →ₗ[ℂ] RSSheafCohomology X G 1 := by
  sorry

end JacobianChallenge.HolomorphicForms
