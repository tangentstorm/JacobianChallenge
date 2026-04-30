import Jacobian.Periods.ChartedFormPullback
import Jacobian.TraceDegree.PullbackFun
import Jacobian.TraceDegree.PullbackFunSmul

/-!
# Bridge: `chartedFormPullback c = pullbackFormsFun c.symm`

The project has two parallel "pullback of a holomorphic 1-form along a
smooth map" definitions:

* `chartedFormPullback c ω e := (ω.toFun (c.symm e)).comp (mfderiv c.symm e)`
  in `Jacobian/Periods/ChartedFormPullback.lean` — pulls back via a
  *chart's inverse* `c.symm : E → X`.
* `pullbackFormsFun f η x := (η.toFun (f x)).comp (mfderiv f x)`
  in `Jacobian/TraceDegree/PullbackFun.lean` — pulls back via an
  *arbitrary smooth map* `f : X → Y`.

When `f := c.symm` (the chart's inverse), these definitions agree
*pointwise by `rfl`*. This file states that connection as a named
lemma, bridging the two infrastructure layers.

## Why this matters

`chartedFormPullback` is the building block for the project's
multi-chart path integration (`pathIntegralViaCoverWith` etc., which
sums chart-local integrals after applying `chartedFormPullback`).
`pullbackFormsFun` is the building block for `pullbackFormsBundledLM`
(the smooth bundled form pullback used in `Jacobian/HolomorphicForms/PullbackBundled.lean`).

This lemma is the **first step** toward connecting:
- the path-level naturality `pathIntegralViaCover_pullbackFormsBundledLM`
  in `Jacobian/Periods/PullbackNaturality.lean`
- with the project's existing chart-by-chart integration infrastructure.

Once this bridge is in place, the path-level naturality proof can
proceed: in each chart, `pathIntegralViaChartCorrect c (f^*η) γᵢ` (which
uses `chartedFormPullback`) corresponds to `pathIntegralInChart c'`-style
integration of `η`'s chart-pullback through `f`, where `c'` is the
composite chart on `Y`.
-/

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms
open JacobianChallenge.TraceDegree

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- The chart-symm pullback of a 1-form on `X` to a function on `E`,
viewed as `pullbackFormsFun c.symm η`. Definitionally equal at every
point, via the matching definitions
`chartedFormPullback c ω e := (ω.toFun (c.symm e)).comp (mfderiv c.symm e)`
and
`pullbackFormsFun f η x := (η.toFun (f x)).comp (mfderiv f x)`
specialised to `f := c.symm` and `x := e`. -/
theorem chartedFormPullback_eq_pullbackFormsFun_symm
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    (e : E) :
    chartedFormPullback c ω e = pullbackFormsFun c.symm ω e := rfl

/-- Functional form: the entire `chartedFormPullback c ω` function on
`E` agrees with `pullbackFormsFun c.symm ω` viewed as a function on
`E`. Sorry-free `funext` of the pointwise lemma. -/
theorem chartedFormPullback_eq_pullbackFormsFun
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X) :
    chartedFormPullback c ω = pullbackFormsFun c.symm ω := by
  funext e
  exact chartedFormPullback_eq_pullbackFormsFun_symm c ω e

/-- The chart-symm pullback of the zero form is the zero function on
`E`. Sorry-free via the bridge + `pullbackFormsFun_zero`. -/
@[simp] theorem chartedFormPullback_zero
    (c : OpenPartialHomeomorph X E) :
    chartedFormPullback c (0 : HolomorphicOneForm E X) = 0 := by
  rw [chartedFormPullback_eq_pullbackFormsFun]
  exact pullbackFormsFun_zero c.symm

/-- The chart-symm pullback distributes over addition of forms.
Sorry-free via the bridge + `pullbackFormsFun_add`. -/
theorem chartedFormPullback_add
    (c : OpenPartialHomeomorph X E) (η ζ : HolomorphicOneForm E X) :
    chartedFormPullback c (η + ζ) =
      chartedFormPullback c η + chartedFormPullback c ζ := by
  rw [chartedFormPullback_eq_pullbackFormsFun,
      chartedFormPullback_eq_pullbackFormsFun,
      chartedFormPullback_eq_pullbackFormsFun]
  exact pullbackFormsFun_add c.symm η ζ

/-- The chart-symm pullback distributes over negation of forms.
Sorry-free via the bridge + `pullbackFormsFun_neg`. -/
@[simp] theorem chartedFormPullback_neg
    (c : OpenPartialHomeomorph X E) (η : HolomorphicOneForm E X) :
    chartedFormPullback c (-η) = - chartedFormPullback c η := by
  rw [chartedFormPullback_eq_pullbackFormsFun,
      chartedFormPullback_eq_pullbackFormsFun]
  exact pullbackFormsFun_neg c.symm η

/-- The chart-symm pullback is `ℂ`-scalar-linear in the form.
Sorry-free via the bridge + `pullbackFormsFun_smul`. -/
@[simp] theorem chartedFormPullback_smul
    (c : OpenPartialHomeomorph X E) (k : ℂ) (η : HolomorphicOneForm E X) :
    chartedFormPullback c (k • η) = k • chartedFormPullback c η := by
  rw [chartedFormPullback_eq_pullbackFormsFun,
      chartedFormPullback_eq_pullbackFormsFun]
  exact pullbackFormsFun_smul c.symm k η

/-- Subtraction case, derived from add + neg. Sorry-free. -/
@[simp] theorem chartedFormPullback_sub
    (c : OpenPartialHomeomorph X E) (η ζ : HolomorphicOneForm E X) :
    chartedFormPullback c (η - ζ) =
      chartedFormPullback c η - chartedFormPullback c ζ := by
  rw [sub_eq_add_neg, sub_eq_add_neg, chartedFormPullback_add,
      chartedFormPullback_neg]

end JacobianChallenge.Periods
