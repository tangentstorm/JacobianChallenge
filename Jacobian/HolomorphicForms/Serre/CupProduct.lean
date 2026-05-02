import Jacobian.HolomorphicForms.Serre.TensorSheaf
import Jacobian.HolomorphicForms.Serre.CanonicalDual
import Jacobian.HolomorphicForms.Serre.CupProductYoneda

/-!
# Cup product on sheaf cohomology (refined)

Round 10 refinement: `serreCupProductH0H1` is now assembled from the
additive-group-level Yoneda cup product `cupProductYonedaH0H1` and
the `ℂ`-bilinearity witness `cupProductYonedaH0H1_isLinear`.

The assembly uses `LinearMap.mk₂` to package the four bilinearity
clauses into a `H⁰ →ₗ[ℂ] H¹ →ₗ[ℂ] H¹(F ⊗ G)` map. Two of the four
clauses come from `AddMonoidHom`-additivity (left/right);
two come from the scalar-compatibility witness.
-/

namespace JacobianChallenge.HolomorphicForms

open scoped Manifold
open CategoryTheory

/-- **Refined (round 10).** Cup product
`H⁰(X, F) × H¹(X, G) → H¹(X, F ⊗ G)`, packaged as a `ℂ`-bilinear map.

Body assembled from `cupProductYonedaH0H1` (the additive-group form)
and `cupProductYonedaH0H1_isLinear` (the scalar compatibility). -/
noncomputable def serreCupProductH0H1
    (X : Type*) [TopologicalSpace X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (F G : RSAbSheaf X)
    [_mF0 : Module ℂ (RSSheafCohomology X F 0)]
    [_mG1 : Module ℂ (RSSheafCohomology X G 1)]
    [_mFG1 : Module ℂ (RSSheafCohomology X (RSTensorAbSheaf X F G) 1)] :
    RSSheafCohomology X F 0 →ₗ[ℂ]
      RSSheafCohomology X G 1 →ₗ[ℂ]
        RSSheafCohomology X (RSTensorAbSheaf X F G) 1 :=
  LinearMap.mk₂ ℂ
    (fun a b => cupProductYonedaH0H1 X F G a b)
    (fun a₁ a₂ b => by simp)
    (fun c a b => (cupProductYonedaH0H1_isLinear X F G c a b).1)
    (fun a b₁ b₂ => (cupProductYonedaH0H1 X F G a).map_add b₁ b₂)
    (fun c a b => (cupProductYonedaH0H1_isLinear X F G c a b).2)

end JacobianChallenge.HolomorphicForms
