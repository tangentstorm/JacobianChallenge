import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Smooth real structure underlying a complex curve

This file records the Stage B1 bridge used by the polygonal-model plan: a
complex one-dimensional manifold carries the induced smooth real
two-dimensional manifold structure.  The construction is by composing complex
charts with the real-coordinate equivalence `Complex.equivRealProd` and the
identification of `ℝ × ℝ` with `EuclideanSpace ℝ (Fin 2)`.
-/

noncomputable section

open scoped Manifold

namespace JacobianChallenge.Periods

/-- The continuous linear equivalence identifying `ℝ × ℝ` with the real
Euclidean model space `EuclideanSpace ℝ (Fin 2)`. -/
def realProdEquivReal2 : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  ((WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).trans (LinearEquiv.finTwoArrow ℝ ℝ)).symm.toContinuousLinearEquiv

/-- The fixed real-coordinate equivalence used to turn complex charts into
charts valued in `EuclideanSpace ℝ (Fin 2)`.  Its underlying map is
`Complex.equivRealProd`, followed by the standard `ℝ × ℝ` to `ℝ²`
identification. -/
def complexEquivReal2 : ℂ ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Complex.equivRealProdCLM.trans realProdEquivReal2

@[simp]
theorem complexEquivReal2_apply (z : ℂ) :
    complexEquivReal2 z = WithLp.toLp 2 ![z.re, z.im] := by
  ext i;
  fin_cases i <;> aesop

/-- The real charted-space structure on `ℂ` obtained from
`complexEquivReal2`, equivalently from `Complex.equivRealProd` followed by the
standard identification of `ℝ × ℝ` with `ℝ²`. -/
def complexChartedSpaceReal2 : ChartedSpace (EuclideanSpace ℝ (Fin 2)) ℂ :=
  complexEquivReal2.toHomeomorph.toOpenPartialHomeomorph.singletonChartedSpace
    (by simp [Homeomorph.toOpenPartialHomeomorph])

/-- Bundled real 2-manifold structure on a complex 1-manifold:
both the `ChartedSpace` witness and the smoothness proof, packaged so
the typeclass piping is self-contained. -/
structure SmoothReal2Structure
    (X : Type*) [TopologicalSpace X] : Type _ where
  chartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 2)) X
  isManifold :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) X := chartedSpace
    IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (⊤ : WithTop ℕ∞) X

private theorem complexEquivReal2_contDiff :
    ContDiff ℝ ⊤ complexEquivReal2 :=
  complexEquivReal2.contDiff

private theorem complexEquivReal2_symm_contDiff :
    ContDiff ℝ ⊤ complexEquivReal2.symm :=
  complexEquivReal2.symm.contDiff

/-- Every chart in the singleton atlas on ℂ equals the standard chart. -/
private theorem singleton_atlas_eq
    (e : OpenPartialHomeomorph ℂ (EuclideanSpace ℝ (Fin 2)))
    (he : e ∈ complexChartedSpaceReal2.atlas) :
    e = complexEquivReal2.toHomeomorph.toOpenPartialHomeomorph := by
  exact complexEquivReal2.toHomeomorph.toOpenPartialHomeomorph.singletonChartedSpace_mem_atlas_eq
    (by simp [Homeomorph.toOpenPartialHomeomorph]) e he

/-
A complex one-manifold has an induced smooth real two-manifold structure.
-/
theorem ChartedSpaceComplex_to_smoothReal2
    (X : Type*) [TopologicalSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) ⊤ X] :
    Nonempty (SmoothReal2Structure X) := by
  classical
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) ℂ := complexChartedSpaceReal2
  letI cs : ChartedSpace (EuclideanSpace ℝ (Fin 2)) X :=
    ChartedSpace.comp (EuclideanSpace ℝ (Fin 2)) ℂ X
  refine ⟨{ chartedSpace := cs, isManifold := ?_ }⟩
  apply isManifold_of_contDiffOn
  intro e e' he he'
  -- Charts in the composed atlas are of the form e₁ ≫ₕ b where e₁ ∈ atlas ℂ X
  -- and b ∈ atlas (EuclideanSpace ℝ (Fin 2)) ℂ.
  -- Since the atlas on ℂ is a singleton, all b are equal to complexEquivReal2.toHomeomorph.toOpenPartialHomeomorph.
  obtain ⟨e₁, he₁, b, hb, rfl⟩ := he
  obtain ⟨e₂, he₂, c, hc, rfl⟩ := he'
  have hb_eq := singleton_atlas_eq b hb
  have hc_eq := singleton_atlas_eq c hc
  subst hb_eq; subst hc_eq
  -- Now the transition map is:
  -- complexEquivReal2 ∘ (e₁.symm.trans e₂) ∘ complexEquivReal2.symm
  -- on the appropriate domain. This is smooth because:
  -- 1. The complex transition e₁.symm.trans e₂ is ContDiffOn ℂ ⊤ (from IsManifold ℂ),
  --    hence ContDiffOn ℝ ⊤ by restrict_scalars
  -- 2. complexEquivReal2 and its symm are ContDiff ℝ ⊤ (continuous linear equivs)
  have h_complex : ContDiffOn ℂ ⊤ (e₂ ∘ e₁.symm) (e₁.symm ≫ₕ e₂).source := by
    have := ‹IsManifold ( modelWithCornersSelf ℂ ℂ ) ⊤ X›.compatible he₁ he₂;
    convert this.1;
    ext; simp [contDiffPregroupoid];
  convert h_complex.restrict_scalars ℝ |> ContDiffOn.comp <| ( show ContDiffOn ℝ ⊤ ( fun x : EuclideanSpace ℝ ( Fin 2 ) => complexEquivReal2.symm x ) _ from ?_ ) using 1;
  rotate_left;
  exact ( e₁ ≫ₕ complexEquivReal2.toHomeomorph.toOpenPartialHomeomorph ).symm ≫ₕ e₂ ≫ₕ complexEquivReal2.toHomeomorph.toOpenPartialHomeomorph |> fun f => f.source;
  · exact complexEquivReal2_symm_contDiff.contDiffOn;
  · constructor <;> intro h <;> simp_all +decide [ Set.MapsTo ];
    · exact ContDiffOn.comp ( h_complex.restrict_scalars ℝ ) ( complexEquivReal2_symm_contDiff.contDiffOn ) fun x hx => by aesop;
    · convert h.continuousLinearMap_comp ( complexEquivReal2.toContinuousLinearMap ) using 1

end JacobianChallenge.Periods