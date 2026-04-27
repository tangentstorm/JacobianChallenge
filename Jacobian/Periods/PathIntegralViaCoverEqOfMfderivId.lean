import Jacobian.Periods.PathIntegralViaCoverPick
import Jacobian.Periods.PathIntegralViaCoverWithEqOfMfderivId

/-!
# Pick-layer bridge under global `mfderiv (chartAt _).symm = id`

Lifts the cover-with bridge to the user-facing `pathIntegralViaCover`
wrapper. Under the global hypothesis that `mfderiv c.symm` is the
identity for every chart's `c.symm` at every model-space point, the
unparameterised multi-chart integral coincides with the
provisional-via-chart sum on whatever partition `Classical.choose`
selects for `γ`.

This is the top of the bridge ladder: chartedForm ✓, in-chart ✓,
via-chart ✓, cover-with ✓, Pick ✓.
-/

namespace JacobianChallenge.Periods

open Set unitInterval JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Under the global hypothesis that `mfderiv c.symm = id` for every
chart at every model-space point, the unparameterised multi-chart
integral can be computed via the provisional via-chart formula on
the `Classical.choose`-picked partition for `γ`. -/
theorem pathIntegralViaCover_eq_sum_provisional_of_mfderiv_id
    (ω : HolomorphicOneForm E X) {a b : X} (γ : Path a b)
    (hd : ∀ (x : X) (e : E),
      mfderiv (modelWithCornersSelf ℂ E)
              (modelWithCornersSelf ℂ E)
              (chartAt E x).symm e =
        ContinuousLinearMap.id ℂ E) :
    pathIntegralViaCover ω γ =
      let h0 := exists_uniform_chart_partition E γ.toContinuousMap
      let h1 := h0.choose_spec
      let h2 := h1.choose_spec
      ∑ i : Fin h0.choose,
        pathIntegralViaChart (chartAt E (h2.choose i)) ω
          (γ.subpath (divFinIcc h0.choose h1.choose i.val
                                (le_of_lt i.isLt))
                     (divFinIcc h0.choose h1.choose (i.val + 1)
                                i.isLt))
          (cover_segment_subpath_range γ h0.choose h1.choose
            h2.choose h2.choose_spec i) := by
  unfold pathIntegralViaCover
  exact pathIntegralViaCoverWith_eq_sum_provisional_of_mfderiv_id
    ω γ _ _ _ _ (fun i e => hd _ e)

end JacobianChallenge.Periods
