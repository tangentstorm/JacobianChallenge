import Jacobian.Periods.ChartedFormPullbackTranslationChart
import Jacobian.Periods.PathIntegralTranslationChart
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Defs

/-!
# The translation `OpenPartialHomeomorph` on `E`

Concrete translation chart `translationChart v : OpenPartialHomeomorph E E`
built from `Homeomorph.addRight v`. We verify its forward and
inverse functions are the expected translations, and apply the
translation-chart bridge to it unconditionally.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) E]

/-- Translation by `v : E`, as an `OpenPartialHomeomorph E E`. -/
def translationChart (v : E) : OpenPartialHomeomorph E E :=
  (Homeomorph.addRight v).toOpenPartialHomeomorph

set_option linter.unusedSectionVars false in
/-- The forward map of the translation chart. -/
@[simp] theorem translationChart_apply (v x : E) :
    translationChart v x = x + v := rfl

set_option linter.unusedSectionVars false in
/-- The inverse of the translation chart. -/
@[simp] theorem translationChart_symm_apply (v x : E) :
    (translationChart v).symm x = x + (-v) := rfl

/-- Concrete bridge instance: corrected and provisional chart-pullbacks
agree on the translation chart. -/
theorem chartedFormPullback_translationChart_eq_chartedForm
    (v : E) (ω : HolomorphicOneForm E E) (e : E) :
    chartedFormPullback (translationChart v) ω e =
      chartedForm (translationChart v) ω e := by
  apply chartedFormPullback_eq_chartedForm_of_symm_eq_add_const
    (translationChart v) ω e (-v)
  funext x
  rfl

/-- In-chart corrected = provisional integral on the translation chart. -/
theorem pathIntegralInChartCorrect_translationChart_eq_pathIntegralInChart
    (v : E) (ω : HolomorphicOneForm E E) {a b : E} (γ : Path a b) :
    pathIntegralInChartCorrect (translationChart v) ω γ =
      pathIntegralInChart (translationChart v) ω γ := by
  apply pathIntegralInChartCorrect_eq_pathIntegralInChart_of_symm_eq_add_const
    (translationChart v) ω γ (-v)
  funext x
  rfl

/-- Via-chart corrected = provisional integral on the translation chart. -/
theorem pathIntegralViaChartCorrect_translationChart_eq_pathIntegralViaChart
    (v : E) (ω : HolomorphicOneForm E E) {a b : E} (γ : Path a b)
    (h : Set.range γ ⊆ (translationChart v).source) :
    pathIntegralViaChartCorrect (translationChart v) ω γ h =
      pathIntegralViaChart (translationChart v) ω γ h := by
  apply pathIntegralViaChartCorrect_eq_pathIntegralViaChart_of_symm_eq_add_const
    (translationChart v) ω γ h (-v)
  funext x
  rfl

set_option linter.unusedSectionVars false in
/-- Function-level transition: composing the inverse of `translationChart u`
with `translationChart v` is itself a translation by `v + (-u)`. This is
the geometric content of why translation atlases close under chart
transitions (the torus structure relies on this). -/
@[simp] theorem translationChart_apply_translationChart_symm_apply
    (u v x : E) :
    translationChart v ((translationChart u).symm x) = x + (-u) + v := rfl

set_option linter.unusedSectionVars false in
/-- Conversely, applying `translationChart u`'s inverse after
`translationChart v` is a translation by `(-u) + v`. -/
@[simp] theorem translationChart_symm_apply_translationChart_apply
    (u v x : E) :
    (translationChart u).symm (translationChart v x) = (x + v) + (-u) := rfl

set_option linter.unusedSectionVars false in
/-- The inverse of `translationChart v`, applied as a function,
agrees pointwise with `translationChart (-v)`. (Both equal
`x ↦ x + (-v)` definitionally.) -/
theorem translationChart_symm_apply_eq_translationChart_neg_apply
    (v x : E) :
    (translationChart v).symm x = translationChart (-v) x := rfl

set_option linter.unusedSectionVars false in
/-- The translation chart's source is all of `E`. -/
@[simp] theorem translationChart_source (v : E) :
    (translationChart v).source = Set.univ := rfl

set_option linter.unusedSectionVars false in
/-- The translation chart's target is all of `E`. -/
@[simp] theorem translationChart_target (v : E) :
    (translationChart v).target = Set.univ := rfl

set_option linter.unusedSectionVars false in
/-- The inverse of a translation chart is the translation chart at
the negated translation, as `OpenPartialHomeomorph`s. -/
theorem translationChart_symm (v : E) :
    (translationChart v).symm = translationChart (-v) := by
  refine OpenPartialHomeomorph.ext _ _ (fun _ => rfl) (fun x => ?_) rfl
  show x + v = x + (- -v)
  rw [neg_neg]

set_option linter.unusedSectionVars false in
/-- The translation chart at zero is the identity (refl) chart. -/
theorem translationChart_zero :
    translationChart (0 : E) = OpenPartialHomeomorph.refl E := by
  refine OpenPartialHomeomorph.ext _ _ (fun x => ?_) (fun x => ?_) rfl
  · show x + 0 = x
    rw [add_zero]
  · show x + (-0) = x
    rw [neg_zero, add_zero]

set_option linter.unusedSectionVars false in
/-- Applying `translationChart (-v)` after `translationChart v`
recovers `x`. (Cancellation law for translations.) -/
@[simp] theorem translationChart_neg_apply_translationChart_apply
    (v x : E) :
    translationChart (-v) (translationChart v x) = x := by
  show (x + v) + (-v) = x
  rw [add_neg_cancel_right]

set_option linter.unusedSectionVars false in
/-- Applying `translationChart v` after `translationChart (-v)`
recovers `x`. -/
@[simp] theorem translationChart_apply_translationChart_neg_apply
    (v x : E) :
    translationChart v (translationChart (-v) x) = x := by
  show (x + (-v)) + v = x
  rw [neg_add_cancel_right]

set_option linter.unusedSectionVars false in
/-- Lifting a path through the translation chart at `v` evaluates
to `γ t + v`. (The chart-lift is just translation by `v` applied
pointwise to the path's image.) -/
@[simp] theorem chartLift_translationChart_apply
    (v : E) {a b : E} (γ : Path a b)
    (h : Set.range γ ⊆ (translationChart v).source) (t : unitInterval) :
    chartLift (translationChart v) γ h t = γ t + v := rfl

/-- The provisional chart-form for a translation chart evaluates
to `ω.toFun` shifted by `-v`. -/
theorem chartedForm_translationChart_apply
    (v : E) (ω : HolomorphicOneForm E E) (e : E) :
    chartedForm (translationChart v) ω e = ω.toFun (e + (-v)) := rfl

/-- The corrected chart-pullback on a translation chart agrees with
the simple shifted form `ω.toFun (e + (-v))` (the `mfderiv` factor
is the identity). -/
theorem chartedFormPullback_translationChart_apply
    (v : E) (ω : HolomorphicOneForm E E) (e : E) :
    chartedFormPullback (translationChart v) ω e = ω.toFun (e + (-v)) := by
  rw [chartedFormPullback_translationChart_eq_chartedForm,
      chartedForm_translationChart_apply]

end JacobianChallenge.Periods
