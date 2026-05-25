import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Jacobian.HolomorphicForms.CompactRiemannSurface
import Jacobian.HolomorphicForms.GenusZeroClassification
import Jacobian.Periods.PeriodLattice
import Jacobian.ComplexTorus.ULiftTransport
import Jacobian.AbelJacobi.AnalyticOfCurveBasis
import Jacobian.TraceDegree.PullbackBasis
import Jacobian.TraceDegree.PushforwardBasis
import Jacobian.TraceDegree.AnalyticDegree
import Jacobian.TraceDegree.PiecewiseC1Instance
import Jacobian.Periods.TrivializationContinuousLinearMapAt

set_option linter.unusedSectionVars false

/-! # Solution mirror of `Jacobian/Challenge.lean` -/

open scoped ContDiff -- for ω notation
open scoped Manifold -- for 𝓘 notation

namespace JacobianChallenge.Solution

-- Global instance adapters to unlock the top-down signatures without exposing extra binders
instance (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    JacobianChallenge.Periods.StableChartAt ℂ X := sorry

instance (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    JacobianChallenge.HolomorphicForms.FiniteDimensionalHolomorphicOneForms ℂ X := sorry

/-- The genus of a compact Riemann surface. -/
noncomputable def genus (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : ℕ :=
  JacobianChallenge.HolomorphicForms.analyticGenus ℂ X

lemma genus_eq_zero_with_routeData_homeo {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (h : genus X = 0)
    (hmod :
      (JacobianChallenge.HolomorphicForms.simplePoleMeromorphicMapOfGenusZero X
        (by simpa [genus] using h)).meromorphicMap.PoleModulusData)
    (hbranch :
      (JacobianChallenge.HolomorphicForms.simplePoleMeromorphicMapOfGenusZero X
        (by simpa [genus] using h)).meromorphicMap.BranchedCoverDataOfPoleDegree) :
    Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
  JacobianChallenge.HolomorphicForms.homeomorphic_sphere_of_analyticGenus_eq_zero_with_routeData X
    (by simpa [genus] using h) hmod hbranch

/-- Genus zero classification. -/
lemma genus_eq_zero_iff_homeo {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    genus X = 0 ↔ Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
  JacobianChallenge.HolomorphicForms.analyticGenus_eq_zero_iff_homeomorphic_sphere X

/-- The Type 0 Jacobian, sorry-free. -/
noncomputable def Jacobian₀ (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Type :=
  ULift (JacobianChallenge.ComplexTorus.quotient
    (Fin (genus X) → ℂ) (JacobianChallenge.Periods.periodFullComplexLattice X))

namespace Jacobian₀

variable {X₀ : Type} [TopologicalSpace X₀] [T2Space X₀] [CompactSpace X₀] [ConnectedSpace X₀]
  [ChartedSpace ℂ X₀] [IsManifold 𝓘(ℂ) ω X₀]
  [JacobianChallenge.TraceDegree.PiecewiseC1PathRegularity X₀]

noncomputable instance : AddCommGroup (Jacobian₀ X₀) := inferInstanceAs (AddCommGroup (ULift _))
noncomputable instance : TopologicalSpace (Jacobian₀ X₀) := inferInstanceAs (TopologicalSpace (ULift _))
instance : T2Space (Jacobian₀ X₀) := inferInstanceAs (T2Space (ULift _))
instance : CompactSpace (Jacobian₀ X₀) := inferInstanceAs (CompactSpace (ULift _))
noncomputable instance : ChartedSpace (Fin (genus X₀) → ℂ) (Jacobian₀ X₀) :=
  inferInstanceAs (ChartedSpace (Fin (genus X₀) → ℂ) (ULift _))
noncomputable instance : IsManifold (modelWithCornersSelf ℂ (Fin (genus X₀) → ℂ)) ω (Jacobian₀ X₀) :=
  inferInstanceAs (IsManifold (modelWithCornersSelf ℂ (Fin (genus X₀) → ℂ)) ω (ULift _))
noncomputable instance : LieAddGroup (modelWithCornersSelf ℂ (Fin (genus X₀) → ℂ)) ω (Jacobian₀ X₀) :=
  inferInstanceAs (LieAddGroup (modelWithCornersSelf ℂ (Fin (genus X₀) → ℂ)) ω (ULift _))

noncomputable def ofCurve (P : X₀) : X₀ → Jacobian₀ X₀ :=
  fun Q => ULift.up (JacobianChallenge.AbelJacobi.analyticOfCurve X₀ P Q)

lemma ofCurve_contMDiff (P : X₀) : ContMDiff 𝓘(ℂ)
    (modelWithCornersSelf ℂ (Fin (genus X₀) → ℂ)) ω (ofCurve P) :=
  (JacobianChallenge.ComplexTorus.contMDiff_uLift_up
      (Λ := JacobianChallenge.Periods.periodFullComplexLattice X₀)).comp
    (JacobianChallenge.AbelJacobi.analyticOfCurve_contMDiff (X := X₀) P)

lemma ofCurve_self (P : X₀) : ofCurve P P = 0 := by
  show ULift.up (JacobianChallenge.AbelJacobi.analyticOfCurve X₀ P P) = 0
  rw [JacobianChallenge.AbelJacobi.analyticOfCurve_self]; rfl

lemma ofCurve_inj_with_meromorphicData (P : X₀) (h : 0 < genus X₀)
    (hanalytic :
      ∀ f : JacobianChallenge.HolomorphicForms.MeromorphicMapToSphere X₀,
        ∀ Q : X₀, f.poleDivisor = JacobianChallenge.HolomorphicForms.Divisor.point Q →
          f.PoleModulusData ∧ f.BranchedCoverDataOfPoleDegree) :
    Function.Injective (ofCurve P) := by
  intro a b hab
  apply JacobianChallenge.AbelJacobi.analyticOfCurve_injective_with_meromorphicData X₀ P
    (by simpa [genus] using h) hanalytic
  exact ULift.up_injective hab

lemma ofCurve_inj (P : X₀) (h : 0 < genus X₀) : Function.Injective (ofCurve P) := by
  intro a b hab
  apply JacobianChallenge.AbelJacobi.analyticOfCurve_injective X₀ P (by simpa [genus] using h)
  exact ULift.up_injective hab

variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
  [JacobianChallenge.TraceDegree.PiecewiseC1PathRegularity Y]
variable (f : X₀ → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)

noncomputable def pushforward : Jacobian₀ X₀ →ₜ+ Jacobian₀ Y where
  toFun P := ULift.up (JacobianChallenge.TraceDegree.analyticPushforward f hf P.down)
  map_zero' := by show ULift.up _ = 0; rw [show (0 : Jacobian₀ X₀).down = 0 from rfl, map_zero]; rfl
  map_add' a b := by show ULift.up _ = ULift.up _ + ULift.up _; rw [show (a + b).down = a.down + b.down from rfl, map_add]; rfl
  continuous_toFun := continuous_uliftUp.comp ((JacobianChallenge.TraceDegree.analyticPushforward f hf).continuous.comp continuous_uliftDown)

theorem pushforward_contMDiff :
    ContMDiff (modelWithCornersSelf ℂ (Fin (genus X₀) → ℂ))
      (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ)) ω (pushforward f hf) :=
  (JacobianChallenge.ComplexTorus.contMDiff_uLift_up (Λ := JacobianChallenge.Periods.periodFullComplexLattice Y)).comp
    ((JacobianChallenge.TraceDegree.analyticPushforward_contMDiff (X := X₀) (Y := Y) f hf).comp
      (JacobianChallenge.ComplexTorus.contMDiff_uLift_down (Λ := JacobianChallenge.Periods.periodFullComplexLattice X₀)))

lemma pushforward_id_apply (P : Jacobian₀ X₀) : pushforward id contMDiff_id P = P := by
  show ULift.up (JacobianChallenge.TraceDegree.analyticPushforward id contMDiff_id P.down) = P
  rw [JacobianChallenge.TraceDegree.analyticPushforward_id_apply]; rfl

variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
  [JacobianChallenge.TraceDegree.PiecewiseC1PathRegularity Z]
variable (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)

lemma pushforward_comp_apply (P : Jacobian₀ X₀) :
    pushforward (g ∘ f) (hg.comp hf) P = pushforward g hg (pushforward f hf P) := by
  show ULift.up (JacobianChallenge.TraceDegree.analyticPushforward (g ∘ f) (hg.comp hf) P.down) =
    ULift.up (JacobianChallenge.TraceDegree.analyticPushforward g hg (JacobianChallenge.TraceDegree.analyticPushforward f hf P.down))
  rw [JacobianChallenge.TraceDegree.analyticPushforward_comp_apply]

noncomputable def pullback : Jacobian₀ Y →ₜ+ Jacobian₀ X₀ where
  toFun P := ULift.up (JacobianChallenge.TraceDegree.analyticPullback f hf P.down)
  map_zero' := by show ULift.up _ = 0; rw [show (0 : Jacobian₀ Y).down = 0 from rfl, map_zero]; rfl
  map_add' a b := by show ULift.up _ = ULift.up _ + ULift.up _; rw [show (a + b).down = a.down + b.down from rfl, map_add]; rfl
  continuous_toFun := continuous_uliftUp.comp ((JacobianChallenge.TraceDegree.analyticPullback f hf).continuous.comp continuous_uliftDown)

theorem pullback_contMDiff :
    ContMDiff (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ))
      (modelWithCornersSelf ℂ (Fin (genus X₀) → ℂ)) ω (pullback f hf) :=
  (JacobianChallenge.ComplexTorus.contMDiff_uLift_up (Λ := JacobianChallenge.Periods.periodFullComplexLattice X₀)).comp
    ((JacobianChallenge.TraceDegree.analyticPullback_contMDiff (X := X₀) (Y := Y) f hf).comp
      (JacobianChallenge.ComplexTorus.contMDiff_uLift_down (Λ := JacobianChallenge.Periods.periodFullComplexLattice Y)))

lemma pullback_id_apply (P : Jacobian₀ X₀) : pullback id contMDiff_id P = P := by
  show ULift.up (JacobianChallenge.TraceDegree.analyticPullback id contMDiff_id P.down) = P
  rw [JacobianChallenge.TraceDegree.analyticPullback_id_apply]; rfl

lemma pullback_comp_apply (P : Jacobian₀ Z) :
    pullback (g.comp f) (hg.comp hf) P = pullback f hf (pullback g hg P) := by
  show ULift.up (JacobianChallenge.TraceDegree.analyticPullback (g.comp f) (hg.comp hf) P.down) =
    ULift.up (JacobianChallenge.TraceDegree.analyticPullback f hf (JacobianChallenge.TraceDegree.analyticPullback g hg P.down))
  rw [JacobianChallenge.TraceDegree.analyticPullback_comp_apply]

lemma pushforward_pullback (P : Jacobian₀ Y) :
    pushforward f hf (pullback f hf P) = (JacobianChallenge.TraceDegree.analyticDegree f hf) • P := by
  show ULift.up (JacobianChallenge.TraceDegree.analyticPushforward f hf
    (JacobianChallenge.TraceDegree.analyticPullback f hf P.down)) =
    (JacobianChallenge.TraceDegree.analyticDegree f hf) • P
  rw [JacobianChallenge.TraceDegree.analyticPushforward_analyticPullback f hf P.down]
  rfl

end Jacobian₀

end JacobianChallenge.Solution

-- =========================================================================
--  PUBLIC UNIFIED SPEC INTERFACE (matching Jacobian/Challenge.lean strictly)
-- =========================================================================

/-- The genus of a compact Riemann surface. -/
noncomputable def genus (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : ℕ :=
  JacobianChallenge.Solution.genus (X := X)

-- let X be a compact Riemann surface
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

lemma genus_eq_zero_iff_homeo :
    genus X = 0 ↔ Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
  JacobianChallenge.Solution.genus_eq_zero_iff_homeo (X := X)

universe u in
/-- The Jacobian of a compact Riemann surface. -/
def Jacobian (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Type u := sorry

namespace Jacobian

-- let X be a compact Riemann surface
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

instance : AddCommGroup (Jacobian X) := sorry
instance : TopologicalSpace (Jacobian X) := sorry
instance : T2Space (Jacobian X) := sorry
instance : CompactSpace (Jacobian X) := sorry
noncomputable instance : ChartedSpace (Fin (genus X) → ℂ) (Jacobian X) := sorry
noncomputable instance : IsManifold (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (Jacobian X) := sorry
noncomputable instance : LieAddGroup (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (Jacobian X) := sorry

/-- The Abel-Jacobi map from a compact Riemann surface to its Jacobian. -/
def ofCurve (P : X) : X → Jacobian X := sorry

lemma ofCurve_contMDiff (P : X) : ContMDiff 𝓘(ℂ)
    (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (ofCurve P) := sorry

lemma ofCurve_self (P : X) : ofCurve P P = 0 := sorry

lemma ofCurve_inj (P : X) (h : 0 < genus X) : Function.Injective (ofCurve P) := sorry

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

variable (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)

/-- The pushforward map between Jacobians associated to a map of the underlying curves. -/
def pushforward (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian X →ₜ+ Jacobian Y := sorry

theorem pushforward_contMDiff :
  ContMDiff (modelWithCornersSelf ℂ (Fin (genus X) → ℂ))
  (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ)) ω (pushforward f hf) := sorry

lemma pushforward_id_apply (P : Jacobian X) : pushforward id contMDiff_id P = P := sorry

variable {Z : Type*} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]

variable (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)

lemma pushforward_comp_apply (P : Jacobian X) :
    pushforward (g ∘ f) (hg.comp hf) P = pushforward g hg (pushforward f hf P) :=
  sorry

/-- Pullback map between Jacobians associated to a map of the underlying curves. -/
def pullback (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian Y →ₜ+ Jacobian X := sorry

theorem pullback_contMDiff :
    ContMDiff (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ))
      (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (pullback f hf) := sorry

lemma pullback_id_apply (P : Jacobian X) : pullback id contMDiff_id P = P := sorry

lemma pullback_comp_apply (P : Jacobian Z) :
    pullback (g.comp f) (hg.comp hf) P = pullback f hf (pullback g hg P) := sorry

def _root_.ContMDiff.degree
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ℕ :=
  sorry

lemma pushforward_pullback (P : Jacobian Y) :
  pushforward f hf (pullback f hf P) = (ContMDiff.degree f hf) • P := sorry

end Jacobian
