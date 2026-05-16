import Jacobian.Blueprint.Sec03.PeriodHomologyInvariance
import Mathlib.Algebra.Homology.ShortComplex.Homology

/-!
# Singular chain descent helpers

Shared helpers for descending chain-level ℤ-linear maps through
`(singularChainComplexZ X).sc 1` to homology — i.e., factoring a map
`SingularOneChain X →ₗ[ℤ] C` through `IntegralOneCycle X` whenever it
kills the boundary image.

Extracted from `Jacobian/Periods/PeriodFunctional.lean` to break the
import cycle between `DeRhamComparisonMap.lean` and `PeriodFunctional.lean`
(the latter transitively imports the former through `HodgeDeRhamRank`).

Both consumers (`PeriodFunctional.periodPairing` and
`DeRhamComparisonMap.deRhamComparisonMap1`) use these helpers to wire
chain-level integration into homology-level functionals.
-/

namespace JacobianChallenge.Periods

open CategoryTheory

/-- **Descent proof helper.** If a ℤ-linear map `I` on chains kills the
image of the short-complex boundary `S.f` (for `S = K.sc 1`), then
`S.toCycles ≫ S.iCycles ≫ Im = 0` holds. -/
theorem periodPairing_descent_aux
    {C : ModuleCat ℤ}
    (S : CategoryTheory.ShortComplex (ModuleCat ℤ))
    (Im : S.X₂ ⟶ C)
    (hI : ∀ (s : ↑S.X₁), Im.hom (S.f.hom s) = 0) :
    S.toCycles ≫ S.iCycles ≫ Im = 0 := by
  suffices h : S.f ≫ Im = 0 by
    rw [← CategoryTheory.Category.assoc, S.toCycles_i]; exact h
  apply ModuleCat.hom_ext
  ext s
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
              LinearMap.zero_apply]
  exact hI s

/-- **Bridge: `singularBoundary21` vs `ShortComplex.f`.** The boundary
map `singularBoundary21 X = (K.d 2 1).hom` agrees with `(K.sc 1).f.hom`
up to the propositional equality `(ComplexShape.down ℕ).prev 1 = 2`. -/
theorem singularBoundary_eq_sc_f
    (X : Type) [TopologicalSpace X] :
    let K := JacobianChallenge.Blueprint.Sec03.singularChainComplexZ X
    let S := K.sc 1
    ∀ (s : ↑S.X₁), ∃ (s' : ↑(JacobianChallenge.Blueprint.Sec03.SingularTwoChain X)),
      S.f.hom s = JacobianChallenge.Blueprint.Sec03.singularBoundary21 X s' := by
  unfold Blueprint.Sec03.singularChainComplexZ
  simp +decide [AlgebraicTopology.singularChainComplexFunctor]
  unfold AlgebraicTopology.SSet.singularChainComplexFunctor
  simp +decide
  unfold AlgebraicTopology.alternatingFaceMapComplex
  unfold AlgebraicTopology.AlternatingFaceMapComplex.obj
  simp +decide [ComplexShape.down]
  unfold ChainComplex.of
  simp +decide [ComplexShape.down']
  split_ifs <;> simp_all +decide [ComplexShape.prev]
  exact fun s => ⟨_, rfl⟩

end JacobianChallenge.Periods
