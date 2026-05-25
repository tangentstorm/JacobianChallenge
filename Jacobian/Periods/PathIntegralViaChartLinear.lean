import Jacobian.Periods.PathLift
import Jacobian.Periods.PathIntegralChartLinear

/-!
# Linearity of the provisional `pathIntegralViaChart`

Negation and scalar-multiplication linearity for the provisional
`pathIntegralViaChart` (which uses the simpler `chartedForm` that
drops the `mfderiv` factor — fine for translation-transition charts
like the torus).

Mirrors `Jacobian/Periods/PathIntegralChartCorrectLinear.lean` and
`/PathIntegralChartCorrectSmul.lean` at the corrected layer. The
addition lemma is omitted here too: `curveIntegral_add` requires
`CurveIntegrable` for both summands, which depends on continuity of
`chartedForm c ω` along the chart-lifted path. Becomes unconditional
once Packet F lands at this layer.
-/

namespace JacobianChallenge.Periods

open Set
open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/--
The provisional from-`X` chart-local path integral negates with
the form.
-/
@[simp] theorem pathIntegralViaChart_neg
    (c : OpenPartialHomeomorph X E) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b) (h : range γ ⊆ c.source) :
    pathIntegralViaChart c (-ω) γ h = - pathIntegralViaChart c ω γ h := by
  unfold pathIntegralViaChart
  exact pathIntegralInChart_neg c ω _

/--
The provisional from-`X` chart-local path integral is ℂ-linear
in the form.
-/
@[simp] theorem pathIntegralViaChart_smul
    (c : OpenPartialHomeomorph X E) (k : ℂ) (ω : HolomorphicOneForm E X)
    {a b : X} (γ : Path a b) (h : range γ ⊆ c.source) :
    pathIntegralViaChart c (k • ω) γ h = k • pathIntegralViaChart c ω γ h := by
  unfold pathIntegralViaChart
  exact pathIntegralInChart_smul c k ω _

end JacobianChallenge.Periods
