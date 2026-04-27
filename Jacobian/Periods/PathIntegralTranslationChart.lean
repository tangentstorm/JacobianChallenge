import Jacobian.Periods.ChartedFormPullbackTranslationChart
import Jacobian.Periods.PathIntegralInChartCorrectEqOfMfderivId
import Jacobian.Periods.PathIntegralViaChartCorrectEqOfMfderivId

/-!
# Translation-chart instance: corrected and provisional integrals coincide

Lifts the previous-tick translation-chart bridge up the integration
tower. If a self-chart `c : OpenPartialHomeomorph E E` has
`c.symm = fun x => x + v` (or `fun x => v + x`) as a function, then:
  - `pathIntegralInChartCorrect c ω γ = pathIntegralInChart c ω γ`
  - `pathIntegralViaChartCorrect c ω γ h = pathIntegralViaChart c ω γ h`
both unconditionally.

Each layer feeds the corresponding `mfderiv_*_const_self` translation
witness into the existing layer-wise `_of_mfderiv_id` bridges.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) E]

/-- In-chart corrected = provisional for a right-translation chart. -/
theorem pathIntegralInChartCorrect_eq_pathIntegralInChart_of_symm_eq_add_const
    (c : OpenPartialHomeomorph E E) (ω : HolomorphicOneForm E E)
    {a b : E} (γ : Path a b) (v : E)
    (h : (fun x : E => c.symm x) = (fun x : E => x + v)) :
    pathIntegralInChartCorrect c ω γ =
      pathIntegralInChart c ω γ := by
  apply pathIntegralInChartCorrect_eq_pathIntegralInChart_of_mfderiv_id
  intro e
  rw [show ((c.symm : E → E)) = (fun x => x + v) from h]
  exact mfderiv_add_const_self v e

/-- Via-chart corrected = provisional for a right-translation chart. -/
theorem pathIntegralViaChartCorrect_eq_pathIntegralViaChart_of_symm_eq_add_const
    (c : OpenPartialHomeomorph E E) (ω : HolomorphicOneForm E E)
    {a b : E} (γ : Path a b) (hr : Set.range γ ⊆ c.source) (v : E)
    (h : (fun x : E => c.symm x) = (fun x : E => x + v)) :
    pathIntegralViaChartCorrect c ω γ hr =
      pathIntegralViaChart c ω γ hr := by
  apply pathIntegralViaChartCorrect_eq_pathIntegralViaChart_of_mfderiv_id
  intro e
  rw [show ((c.symm : E → E)) = (fun x => x + v) from h]
  exact mfderiv_add_const_self v e

/-- In-chart corrected = provisional for a left-translation chart. -/
theorem pathIntegralInChartCorrect_eq_pathIntegralInChart_of_symm_eq_const_add
    (c : OpenPartialHomeomorph E E) (ω : HolomorphicOneForm E E)
    {a b : E} (γ : Path a b) (v : E)
    (h : (fun x : E => c.symm x) = (fun x : E => v + x)) :
    pathIntegralInChartCorrect c ω γ =
      pathIntegralInChart c ω γ := by
  apply pathIntegralInChartCorrect_eq_pathIntegralInChart_of_mfderiv_id
  intro e
  rw [show ((c.symm : E → E)) = (fun x => v + x) from h]
  exact mfderiv_const_add_self v e

/-- Via-chart corrected = provisional for a left-translation chart. -/
theorem pathIntegralViaChartCorrect_eq_pathIntegralViaChart_of_symm_eq_const_add
    (c : OpenPartialHomeomorph E E) (ω : HolomorphicOneForm E E)
    {a b : E} (γ : Path a b) (hr : Set.range γ ⊆ c.source) (v : E)
    (h : (fun x : E => c.symm x) = (fun x : E => v + x)) :
    pathIntegralViaChartCorrect c ω γ hr =
      pathIntegralViaChart c ω γ hr := by
  apply pathIntegralViaChartCorrect_eq_pathIntegralViaChart_of_mfderiv_id
  intro e
  rw [show ((c.symm : E → E)) = (fun x => v + x) from h]
  exact mfderiv_const_add_self v e

end JacobianChallenge.Periods
