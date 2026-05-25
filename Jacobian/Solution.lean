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

/-- The genus of a compact Riemann surface. -/
noncomputable def genus (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [JacobianChallenge.HolomorphicForms.FiniteDimensionalHolomorphicOneForms ℂ X] : ℕ :=
  JacobianChallenge.HolomorphicForms.analyticGenus ℂ X

/--
Genus-zero classification along the meromorphic degree-one route, conditional
on the analytic data that promotes the fixed-pole Riemann-Roch map to a
degree-one branched cover.
-/
lemma genus_eq_zero_with_routeData_homeo {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [JacobianChallenge.HolomorphicForms.FiniteDimensionalHolomorphicOneForms ℂ X]
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
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [JacobianChallenge.Periods.StableChartAt ℂ X]
    [JacobianChallenge.HolomorphicForms.FiniteDimensionalHolomorphicOneForms ℂ X] :
    genus X = 0 ↔ Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
  JacobianChallenge.HolomorphicForms.analyticGenus_eq_zero_iff_homeomorphic_sphere X

/-- The Jacobian of a compact Riemann surface. -/
noncomputable def Jacobian (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [JacobianChallenge.Periods.StableChartAt ℂ X]
    [JacobianChallenge.HolomorphicForms.FiniteDimensionalHolomorphicOneForms ℂ X] : Type :=
  ULift (JacobianChallenge.ComplexTorus.quotient
    (Fin (genus X) → ℂ) (JacobianChallenge.Periods.periodFullComplexLattice X))

end JacobianChallenge.Solution

-- let X be a compact Riemann surface
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [JacobianChallenge.Periods.StableChartAt ℂ X]
  [JacobianChallenge.HolomorphicForms.FiniteDimensionalHolomorphicOneForms ℂ X]

noncomputable def genus := JacobianChallenge.Solution.genus (X := X)

lemma genus_eq_zero_with_routeData_homeo
    (h : genus (X := X) = 0)
    (hmod :
      (JacobianChallenge.HolomorphicForms.simplePoleMeromorphicMapOfGenusZero X
        (by simpa [genus] using h)).meromorphicMap.PoleModulusData)
    (hbranch :
      (JacobianChallenge.HolomorphicForms.simplePoleMeromorphicMapOfGenusZero X
        (by simpa [genus] using h)).meromorphicMap.BranchedCoverDataOfPoleDegree) :
    Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
  JacobianChallenge.Solution.genus_eq_zero_with_routeData_homeo (X := X) h hmod hbranch

lemma genus_eq_zero_iff_homeo :
    genus (X := X) = 0 ↔ Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
  JacobianChallenge.Solution.genus_eq_zero_iff_homeo (X := X)

-- Type-0-specialised section for the Jacobian-related declarations.
variable {X₀ : Type} [TopologicalSpace X₀] [T2Space X₀] [CompactSpace X₀] [ConnectedSpace X₀]
  [ChartedSpace ℂ X₀] [IsManifold 𝓘(ℂ) ω X₀] [JacobianChallenge.Periods.StableChartAt ℂ X₀]
  [JacobianChallenge.HolomorphicForms.FiniteDimensionalHolomorphicOneForms ℂ X₀]
  [JacobianChallenge.TraceDegree.PiecewiseC1PathRegularity X₀]

noncomputable def Jacobian := JacobianChallenge.Solution.Jacobian X₀

namespace Jacobian

noncomputable instance : AddCommGroup (Jacobian (X₀ := X₀)) := inferInstanceAs (AddCommGroup (ULift _))
noncomputable instance : TopologicalSpace (Jacobian (X₀ := X₀)) := inferInstanceAs (TopologicalSpace (ULift _))
instance : T2Space (Jacobian (X₀ := X₀)) := inferInstanceAs (T2Space (ULift _))
instance : CompactSpace (Jacobian (X₀ := X₀)) := inferInstanceAs (CompactSpace (ULift _))
noncomputable instance : ChartedSpace (Fin (genus (X := X₀)) → ℂ) (Jacobian (X₀ := X₀)) :=
  inferInstanceAs (ChartedSpace (Fin (genus (X := X₀)) → ℂ) (ULift _))
noncomputable instance : IsManifold (modelWithCornersSelf ℂ (Fin (genus (X := X₀)) → ℂ)) ω (Jacobian (X₀ := X₀)) :=
  inferInstanceAs (IsManifold (modelWithCornersSelf ℂ (Fin (genus (X := X₀)) → ℂ)) ω (ULift _))
noncomputable instance : LieAddGroup (modelWithCornersSelf ℂ (Fin (genus (X := X₀)) → ℂ)) ω (Jacobian (X₀ := X₀)) :=
  inferInstanceAs (LieAddGroup (modelWithCornersSelf ℂ (Fin (genus (X := X₀)) → ℂ)) ω (ULift _))

/-- The Abel-Jacobi map from a compact Riemann surface to its Jacobian. -/
noncomputable def ofCurve (P : X₀) : X₀ → Jacobian (X₀ := X₀) :=
  fun Q => ULift.up (JacobianChallenge.AbelJacobi.analyticOfCurve X₀ P Q)

lemma ofCurve_contMDiff (P : X₀) : ContMDiff 𝓘(ℂ)
    (modelWithCornersSelf ℂ (Fin (genus (X := X₀)) → ℂ)) ω (ofCurve P) :=
  (JacobianChallenge.ComplexTorus.contMDiff_uLift_up
      (Λ := JacobianChallenge.Periods.periodFullComplexLattice X₀)).comp
    (JacobianChallenge.AbelJacobi.analyticOfCurve_contMDiff (X := X₀) P)

lemma ofCurve_self (P : X₀) : ofCurve P P = 0 := by
  show ULift.up (JacobianChallenge.AbelJacobi.analyticOfCurve X₀ P P) = 0
  rw [JacobianChallenge.AbelJacobi.analyticOfCurve_self]; rfl

lemma ofCurve_inj_with_meromorphicData (P : X₀) (h : 0 < genus (X := X₀))
    (hanalytic :
      ∀ f : JacobianChallenge.HolomorphicForms.MeromorphicMapToSphere X₀,
        ∀ Q : X₀, f.poleDivisor = JacobianChallenge.HolomorphicForms.Divisor.point Q →
          f.PoleModulusData ∧ f.BranchedCoverDataOfPoleDegree) :
    Function.Injective (ofCurve P) := by
  intro a b hab
  apply JacobianChallenge.AbelJacobi.analyticOfCurve_injective_with_meromorphicData X₀ P
    (by simpa [genus] using h) hanalytic
  exact ULift.up_injective hab

/-- Public Abel-Jacobi injectivity contract from `Jacobian/Challenge.lean`. -/
lemma ofCurve_inj (P : X₀) (h : 0 < genus (X := X₀)) : Function.Injective (ofCurve P) := by
  intro a b hab
  apply JacobianChallenge.AbelJacobi.analyticOfCurve_injective X₀ P (by simpa [genus] using h)
  exact ULift.up_injective hab

variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] [JacobianChallenge.Periods.StableChartAt ℂ Y]
  [JacobianChallenge.HolomorphicForms.FiniteDimensionalHolomorphicOneForms ℂ Y]
  [JacobianChallenge.TraceDegree.PiecewiseC1PathRegularity Y]
variable (f : X₀ → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)

noncomputable def pushforward : Jacobian (X₀ := X₀) →ₜ+ Jacobian (X₀ := Y) where
  toFun P := ULift.up (JacobianChallenge.TraceDegree.analyticPushforward f hf P.down)
  map_zero' := by show ULift.up _ = 0; rw [show (0 : Jacobian (X₀ := X₀)).down = 0 from rfl, map_zero]; rfl
  map_add' a b := by show ULift.up _ = ULift.up _ + ULift.up _; rw [show (a + b).down = a.down + b.down from rfl, map_add]; rfl
  continuous_toFun := continuous_uliftUp.comp ((JacobianChallenge.TraceDegree.analyticPushforward f hf).continuous.comp continuous_uliftDown)

theorem pushforward_contMDiff :
    ContMDiff (modelWithCornersSelf ℂ (Fin (genus (X := X₀)) → ℂ))
      (modelWithCornersSelf ℂ (Fin (genus (X := Y)) → ℂ)) ω (pushforward f hf) :=
  (JacobianChallenge.ComplexTorus.contMDiff_uLift_up (Λ := JacobianChallenge.Periods.periodFullComplexLattice Y)).comp
    ((JacobianChallenge.TraceDegree.analyticPushforward_contMDiff (X := X₀) (Y := Y) f hf).comp
      (JacobianChallenge.ComplexTorus.contMDiff_uLift_down (Λ := JacobianChallenge.Periods.periodFullComplexLattice X₀)))

lemma pushforward_id_apply (P : Jacobian (X₀ := X₀)) : pushforward id contMDiff_id P = P := by
  show ULift.up (JacobianChallenge.TraceDegree.analyticPushforward id contMDiff_id P.down) = P
  rw [JacobianChallenge.TraceDegree.analyticPushforward_id_apply]; rfl

variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z] [JacobianChallenge.Periods.StableChartAt ℂ Z]
  [JacobianChallenge.HolomorphicForms.FiniteDimensionalHolomorphicOneForms ℂ Z]
  [JacobianChallenge.TraceDegree.PiecewiseC1PathRegularity Z]
variable (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)

lemma pushforward_comp_apply (P : Jacobian (X₀ := X₀)) :
    pushforward (g ∘ f) (hg.comp hf) P = pushforward g hg (pushforward f hf P) := by
  show ULift.up (JacobianChallenge.TraceDegree.analyticPushforward (g ∘ f) (hg.comp hf) P.down) =
    ULift.up (JacobianChallenge.TraceDegree.analyticPushforward g hg (JacobianChallenge.TraceDegree.analyticPushforward f hf P.down))
  rw [JacobianChallenge.TraceDegree.analyticPushforward_comp_apply]

noncomputable def pullback : Jacobian (X₀ := Y) →ₜ+ Jacobian (X₀ := X₀) where
  toFun P := ULift.up (JacobianChallenge.TraceDegree.analyticPullback f hf P.down)
  map_zero' := by show ULift.up _ = 0; rw [show (0 : Jacobian (X₀ := Y)).down = 0 from rfl, map_zero]; rfl
  map_add' a b := by show ULift.up _ = ULift.up _ + ULift.up _; rw [show (a + b).down = a.down + b.down from rfl, map_add]; rfl
  continuous_toFun := continuous_uliftUp.comp ((JacobianChallenge.TraceDegree.analyticPullback f hf).continuous.comp continuous_uliftDown)

theorem pullback_contMDiff :
    ContMDiff (modelWithCornersSelf ℂ (Fin (genus (X := Y)) → ℂ))
      (modelWithCornersSelf ℂ (Fin (genus (X := X₀)) → ℂ)) ω (pullback f hf) :=
  (JacobianChallenge.ComplexTorus.contMDiff_uLift_up (Λ := JacobianChallenge.Periods.periodFullComplexLattice X₀)).comp
    ((JacobianChallenge.TraceDegree.analyticPullback_contMDiff (X := X₀) (Y := Y) f hf).comp
      (JacobianChallenge.ComplexTorus.contMDiff_uLift_down (Λ := JacobianChallenge.Periods.periodFullComplexLattice Y)))

lemma pullback_id_apply (P : Jacobian (X₀ := X₀)) : pullback id contMDiff_id P = P := by
  show ULift.up (JacobianChallenge.TraceDegree.analyticPullback id contMDiff_id P.down) = P
  rw [JacobianChallenge.TraceDegree.analyticPullback_id_apply]; rfl

lemma pullback_comp_apply (P : Jacobian (X₀ := Z)) :
    pullback (g.comp f) (hg.comp hf) P = pullback f hf (pullback g hg P) := by
  show ULift.up (JacobianChallenge.TraceDegree.analyticPullback (g.comp f) (hg.comp hf) P.down) =
    ULift.up (JacobianChallenge.TraceDegree.analyticPullback f hf (JacobianChallenge.TraceDegree.analyticPullback g hg P.down))
  rw [JacobianChallenge.TraceDegree.analyticPullback_comp_apply]

noncomputable def _root_.ContMDiff.degree (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ℕ :=
  JacobianChallenge.TraceDegree.analyticDegree f hf

lemma pushforward_pullback (P : Jacobian (X₀ := Y)) :
    pushforward f hf (pullback f hf P) = (JacobianChallenge.TraceDegree.analyticDegree f hf) • P :=
  by
    show ULift.up (JacobianChallenge.TraceDegree.analyticPushforward f hf
      (JacobianChallenge.TraceDegree.analyticPullback f hf P.down)) =
      (JacobianChallenge.TraceDegree.analyticDegree f hf) • P
    rw [JacobianChallenge.TraceDegree.analyticPushforward_analyticPullback f hf P.down]
    rfl

end Jacobian
