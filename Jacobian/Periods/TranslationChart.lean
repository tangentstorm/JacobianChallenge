import Jacobian.Periods.ChartedFormPullbackTranslationChart
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

end JacobianChallenge.Periods
