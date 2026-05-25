import Jacobian.Periods.ChartedFormLinearMap

/-!
# Pointwise application of `chartedFormLinearMap`

Provisional analogue of `ChartedFormPullbackLinearMapApply.lean` at
the corrected layer.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- The bundled provisional chart-form evaluated at a point. -/
@[simp] theorem chartedFormLinearMap_apply_at
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X) (e : E) :
    chartedFormLinearMap c ω e = chartedForm c ω e := rfl

/--
Applying the bundled provisional chart-form at a chart point and
then at a tangent vector gives the underlying value. (Note: unlike
the corrected layer, the provisional version drops the chart
derivative — fine for translation-transition charts only.)
-/
@[simp] theorem chartedFormLinearMap_apply_vec
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    (e : E) (v : E) :
    chartedFormLinearMap c ω e v = ω.toFun (c.symm e) v := rfl

end JacobianChallenge.Periods
