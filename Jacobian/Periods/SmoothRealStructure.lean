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
def complexChartedSpaceReal2 : ChartedSpace (EuclideanSpace ℝ (Fin 2)) ℂ := by
  -- This is the singleton atlas whose only chart is
  -- `complexEquivReal2.toHomeomorph.toOpenPartialHomeomorph`.
  sorry

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

/-- A complex one-manifold has an induced smooth real two-manifold structure.

The intended construction composes each complex chart with
`complexEquivReal2.toHomeomorph.toOpenPartialHomeomorph`, whose first factor is
Mathlib's `Complex.equivRealProd`.  The compatibility proof is the standard
restriction-of-scalars argument for holomorphic transition maps, followed by
the smoothness of continuous linear equivalences between the real model
spaces.
-/
theorem ChartedSpaceComplex_to_smoothReal2
    (X : Type*) [TopologicalSpace X]
    [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) ⊤ X] :
    Nonempty (SmoothReal2Structure X) := by
  classical
  -- Compose the original complex charts with the fixed real-coordinate chart
  -- `ℂ ≃L[ℝ] EuclideanSpace ℝ (Fin 2)`.
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) ℂ := complexChartedSpaceReal2
  letI cs : ChartedSpace (EuclideanSpace ℝ (Fin 2)) X :=
    ChartedSpace.comp (EuclideanSpace ℝ (Fin 2)) ℂ X
  refine ⟨{ chartedSpace := cs, isManifold := ?_ }⟩
  -- The induced atlas is smooth because holomorphic changes of coordinates
  -- are smooth after restriction of scalars, and the extra chart changes are
  -- continuous linear equivalences.
  sorry

end JacobianChallenge.Periods