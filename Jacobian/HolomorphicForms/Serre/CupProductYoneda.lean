import Jacobian.HolomorphicForms.SheafCohomologyRS
import Jacobian.HolomorphicForms.Serre.TensorSheaf

/-!
# Cup product via the Yoneda/Ext product (frontier)

The cup product on sheaf cohomology is, in Mathlib's Ext-based
formulation, an instance of the Yoneda composition
`Ext^p(F, A) ⊗ Ext^q(B, G) → Ext^{p+q}(F ⊗ B, A ⊗ G)` specialised to
`A = B = trivial unit sheaf`. Round 10 names that specialisation as a
frontier obligation so the cup product API can be expressed in terms
of a single Mathlib hook (when one becomes available) rather than
re-deriving the cup product from scratch.

We expose two named obligations:

1. `cupProductYonedaH0H1` — the additive-group form of the cup
   product on H⁰ × H¹ → H¹ of a tensor sheaf (frontier).
2. `cupProductYonedaH0H1_isLinear` — the `ℂ`-bilinearity / scalar
   compatibility (frontier).

Round 4's `serreCupProductH0H1` then assembles the linear-map form
from these two pieces. The third frontier `Module ℂ` instance on the
cup-product target (`serrePairing_module_H1Tensor`) lives in
`Serre/Pairing.lean`.
-/

namespace JacobianChallenge.HolomorphicForms

open CategoryTheory

/-- **Frontier `def` (sorry).** Additive-group form of the cup
product `H⁰(X, F) × H¹(X, G) → H¹(X, F ⊗ G)`, packaged as a
ℤ-bilinear map between the underlying `AddCommGroup`s.

Will be refined later via Mathlib's Ext-based Yoneda product on
`CategoryTheory.Sheaf` once that API is exposed. -/
noncomputable def cupProductYonedaH0H1
    (X : Type*) [TopologicalSpace X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (F G : RSAbSheaf X) :
    RSSheafCohomology X F 0 →+
      RSSheafCohomology X G 1 →+ RSSheafCohomology X (RSTensorAbSheaf X F G) 1 := by
  sorry

/-- **Frontier theorem (sorry).** The Yoneda cup product is
ℂ-bilinear: scalars on either input pull out of the bilinear form.

Together with the underlying additive map this is enough to bundle
the cup product as a `LinearMap`. -/
theorem cupProductYonedaH0H1_isLinear
    (X : Type*) [TopologicalSpace X]
    [HasSheafify (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0}]
    [HasExt.{0} (Sheaf (Opens.grothendieckTopology (TopCat.of X)) AddCommGrpCat.{0})]
    (F G : RSAbSheaf X)
    [_mF0 : Module ℂ (RSSheafCohomology X F 0)]
    [_mG1 : Module ℂ (RSSheafCohomology X G 1)]
    [_mFG1 : Module ℂ (RSSheafCohomology X (RSTensorAbSheaf X F G) 1)] :
    ∀ (c : ℂ) (a : RSSheafCohomology X F 0)
       (b : RSSheafCohomology X G 1),
      cupProductYonedaH0H1 X F G (c • a) b = c • cupProductYonedaH0H1 X F G a b ∧
      cupProductYonedaH0H1 X F G a (c • b) = c • cupProductYonedaH0H1 X F G a b := by
  sorry

end JacobianChallenge.HolomorphicForms
