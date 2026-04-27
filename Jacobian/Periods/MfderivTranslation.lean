import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Complex.Basic

/-!
# Translation has identity manifold derivative

For a translation `x ↦ x + v` (or `x ↦ v + x`) on the model space
`E`, the manifold derivative is the identity continuous linear map.
This is the key reason translation-transition charts make the
provisional and corrected chart-form layers coincide
unconditionally.

Proof: reduce to `fderiv` via `mfderiv_eq_fderiv` (applicable because
the source/target are model spaces), then `fderiv_add_const` +
`fderiv_id`.
-/

namespace JacobianChallenge.Periods

open scoped Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The manifold derivative of right-translation `x ↦ x + v` is the
identity at every point. -/
theorem mfderiv_add_const_self (v e : E) :
    mfderiv (modelWithCornersSelf ℂ E)
            (modelWithCornersSelf ℂ E)
            (fun x : E => x + v) e =
      ContinuousLinearMap.id ℂ E := by
  rw [mfderiv_eq_fderiv, fderiv_add_const]
  exact fderiv_id

/-- The manifold derivative of left-translation `x ↦ v + x` is the
identity at every point. -/
theorem mfderiv_const_add_self (v e : E) :
    mfderiv (modelWithCornersSelf ℂ E)
            (modelWithCornersSelf ℂ E)
            (fun x : E => v + x) e =
      ContinuousLinearMap.id ℂ E := by
  rw [mfderiv_eq_fderiv, fderiv_const_add]
  exact fderiv_id

/-- The manifold derivative of `x ↦ x - v` is the identity at every
point. (Specializes `mfderiv_add_const_self` with `-v`.) -/
theorem mfderiv_sub_const_self (v e : E) :
    mfderiv (modelWithCornersSelf ℂ E)
            (modelWithCornersSelf ℂ E)
            (fun x : E => x - v) e =
      ContinuousLinearMap.id ℂ E := by
  have : (fun x : E => x - v) = (fun x : E => x + (-v)) := by
    funext x; rw [sub_eq_add_neg]
  rw [this]
  exact mfderiv_add_const_self (-v) e

end JacobianChallenge.Periods
