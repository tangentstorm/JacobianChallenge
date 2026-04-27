import Jacobian.Periods.ChartedForm
import Jacobian.Periods.ChartedFormPullback

/-!
# `chartedFormPullback` factors through `chartedForm` and `mfderiv`

The genuine chart-pullback `chartedFormPullback c ω e` is by
definition `(ω.toFun (c.symm e)).comp (mfderiv c.symm e)`, while
the provisional `chartedForm c ω e` is just `ω.toFun (c.symm e)`.
So `chartedFormPullback c ω e = (chartedForm c ω e).comp
(mfderiv c.symm e)` definitionally.

This identity makes the difference between the two layers explicit
as a single `comp`-factor, and is the cleanest bridge between the
provisional and corrected chart-form towers. Both forms are equal
exactly when the `mfderiv` factor is the identity (e.g. for
translation-transition charts on `ℂ` itself).
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- The genuine chart pullback equals the provisional chart-form
post-composed with the manifold derivative of `c.symm`. -/
theorem chartedFormPullback_eq_chartedForm_comp_mfderiv
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X) (e : E) :
    chartedFormPullback c ω e =
      (chartedForm c ω e).comp
        (mfderiv (modelWithCornersSelf ℂ E)
                 (modelWithCornersSelf ℂ E) c.symm e) := rfl

/-- Vector-apply form: the genuine chart pullback at `(e, v)` equals
the provisional chart-form at `e` evaluated on `mfderiv c.symm e v`. -/
theorem chartedFormPullback_apply_eq_chartedForm_apply_mfderiv
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    (e v : E) :
    chartedFormPullback c ω e v =
      chartedForm c ω e
        (mfderiv (modelWithCornersSelf ℂ E)
                 (modelWithCornersSelf ℂ E) c.symm e v) := rfl

end JacobianChallenge.Periods
