import Jacobian.Periods.PathIntegralViaChartCorrect
import Jacobian.HolomorphicForms.PullbackBundled

/-!
# Chart-level chain rule for `pathIntegralViaChartCorrect`

**Phase 5 deliverable** of the path-integral well-definedness chain.

States: when a path `γ` on `X` lies in a chart `chartAt ℂ p` and the
mapped path `γ.map hf.continuous` lies in a chart `chartAt ℂ q` on `Y`,
the chart-corrected integral of the form-pullback agrees with the
chart-corrected integral of the original form along the mapped path:

  `pathIntegralViaChartCorrect (chartAt ℂ p)
       (pullbackFormsBundledLM X Y f hf η) γ hX =
   pathIntegralViaChartCorrect (chartAt ℂ q) η
       (γ.map hf.continuous) hY`.

This is the **single named analytic gap** of Phase 5 (the genuine
chain rule for the chart pullback). Once discharged, both Sorry 2
(`pathIntegralViaCover_pullback_chart_segment`, the un-`With`
single-chart statement) and Sorry 5
(`pathIntegralViaCoverWith_pullback_via_common_partition`, the
multi-segment assembly) become sorry-free reductions.

## Mathematical content

Unfolding both sides:

  LHS = `curveIntegral (chartedFormPullback (chartAt ℂ p)
           (pullbackFormsBundledLM X Y f hf η)) (chartLift (chartAt ℂ p) γ hX)`

  RHS = `curveIntegral (chartedFormPullback (chartAt ℂ q) η)
           (chartLift (chartAt ℂ q) (γ.map hf.continuous) hY)`

The chart-lifted paths are related by the chart transition
`(chartAt ℂ q) ∘ f ∘ (chartAt ℂ p).symm`, which is smooth on the
overlap (chart-transition smoothness from `[IsManifold ⊤]` plus
smoothness of `f`).

The integrand transformation:

  `chartedFormPullback (chartAt ℂ p) (pullbackFormsBundledLM X Y f hf η) e` =
  `(η.toFun (f ((chartAt ℂ p).symm e))).comp (mfderiv f ((chartAt ℂ p).symm e))
     .comp (mfderiv (chartAt ℂ p).symm e)`

equals the chart-pullback of `η` at `q` precomposed with the
chart-transition derivative — i.e. the chain rule for `mfderiv`
applied to the composition `(chartAt ℂ q) ∘ f ∘ (chartAt ℂ p).symm`.

The integral identity then follows from the change-of-variables
formula for `intervalIntegral` applied to this smooth chart
transition. Roughly the same depth as Mathlib's `mfderiv_comp` plus
`intervalIntegral.integral_comp_smul_deriv` for the smooth
diffeomorphism case.

## Status

A single named sorry. Estimated effort: 7–10 days. Once discharged:

* `Sorry 5` in `PullbackNaturality.lean` becomes a sum-congruence
  using this lemma per segment (see `pullback_via_common_partition_via`
  below).
* `Sorry 2` in `PullbackNaturality.lean` becomes a single-chart
  unfolding of `pathIntegralViaCover` reducing to this lemma.
-/

namespace JacobianChallenge.Periods

open Set unitInterval JacobianChallenge.HolomorphicForms

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) X]
variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold (modelWithCornersSelf ℂ ℂ) (⊤ : WithTop ℕ∞) Y]

open scoped Manifold ContDiff

/-- **Phase 5 (single named gap): chart-level chain rule for the
chart-corrected path integral.**

For a smooth `f : X → Y` and a holomorphic 1-form `η` on `Y`, when
`γ : Path a b` on `X` lies in a single chart of `X` and the mapped
path `γ.map hf.continuous` lies in a single chart of `Y`, the
chart-corrected integral of the form-pullback equals the chart-
corrected integral of the original form along the mapped path.

This is the genuine analytic content. See file-level docstring for
the proof outline (chain rule for `mfderiv` + change of variables
for `intervalIntegral` on the chart transition). -/
theorem pathIntegralViaChartCorrect_pullbackFormsBundledLM
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (η : HolomorphicOneForm ℂ Y) (p : X) (q : Y)
    {a b : X} (γ : Path a b)
    (hX : range γ ⊆ (chartAt ℂ p).source)
    (hY : range (γ.map hf.continuous) ⊆ (chartAt ℂ q).source) :
    pathIntegralViaChartCorrect (chartAt ℂ p)
        (pullbackFormsBundledLM X Y f hf η) γ hX =
      pathIntegralViaChartCorrect (chartAt ℂ q) η
        (γ.map hf.continuous) hY := by
  sorry

end JacobianChallenge.Periods
