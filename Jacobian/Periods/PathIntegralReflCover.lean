import Jacobian.Periods.PathIntegralReflChart
import Jacobian.Periods.PathIntegralViaCoverWithEqOfMfderivId
import Jacobian.Periods.PathIntegralViaCoverEqOfMfderivId

/-!
# Refl-chart instance: cover-level corrected = provisional sum

For `chartedSpaceSelf E` (every `chartAt E x` is
`OpenPartialHomeomorph.refl E`), the cover-with and Pick-layer
bridges fire unconditionally. Each segment chart is the refl chart,
whose `mfderiv c.symm = id` everywhere — packaged as
`mfderiv_refl_symm_eq_id`.

Top of the refl-chart pipeline: combines
`pathIntegralViaCover{With,}_eq_sum_provisional_of_mfderiv_id` with
the refl-chart witness.
-/

namespace JacobianChallenge.Periods

open Set unitInterval JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) E]

/-- For `chartedSpaceSelf E`, the cover-with multi-chart integral
equals the sum of provisional via-chart integrals on each segment,
unconditionally. -/
theorem pathIntegralViaCoverWith_self_eq_sum_provisional
    (ω : HolomorphicOneForm E E) {a b : E} (γ : Path a b)
    (n : ℕ) (hn : 0 < n) (pickChart : Fin n → E)
    (hcov : ∀ (i : Fin n) (t : unitInterval),
      (i : ℝ) / n ≤ (t : ℝ) → (t : ℝ) ≤ ((i : ℝ) + 1) / n →
      γ t ∈ (chartAt E (pickChart i)).source) :
    pathIntegralViaCoverWith ω γ n hn pickChart hcov =
      ∑ i : Fin n,
        pathIntegralViaChart (chartAt E (pickChart i)) ω
          (γ.subpath (divFinIcc n hn i.val (le_of_lt i.isLt))
                     (divFinIcc n hn (i.val + 1) i.isLt))
          (cover_segment_subpath_range γ n hn pickChart hcov i) :=
  pathIntegralViaCoverWith_eq_sum_provisional_of_mfderiv_id
    ω γ n hn pickChart hcov (fun _ e => mfderiv_refl_symm_eq_id e)

/-- For `chartedSpaceSelf E`, the user-facing
`pathIntegralViaCover` equals the sum of provisional via-chart
integrals on the `Classical.choose`-picked partition,
unconditionally. -/
theorem pathIntegralViaCover_self_eq_sum_provisional
    (ω : HolomorphicOneForm E E) {a b : E} (γ : Path a b) :
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
            h2.choose h2.choose_spec i) :=
  pathIntegralViaCover_eq_sum_provisional_of_mfderiv_id
    ω γ (fun _ e => mfderiv_refl_symm_eq_id e)

end JacobianChallenge.Periods
