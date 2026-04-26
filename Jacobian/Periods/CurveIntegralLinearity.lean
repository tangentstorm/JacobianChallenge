import Jacobian.Periods.ChartedFormPullbackLinearMap
import Jacobian.Periods.PathIntegralChartCorrect
import Jacobian.Periods.PathIntegralChartCorrectZero
import Jacobian.Periods.PathIntegralChartCorrectLinear
import Jacobian.Periods.PathIntegralChartCorrectSmul

namespace JacobianChallenge.Periods

open JacobianChallenge.HolomorphicForms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
  [IsManifold (modelWithCornersSelf ℂ E) (⊤ : WithTop ℕ∞) X]

/-- Reserved file: when `_add` lands (Packet F:
`chartedFormPullback_curveIntegrable`), this file will package
`pathIntegralInChartCorrect c · γ` as a `HolomorphicOneForm E X →+ ℂ`
via the structure literal pattern used by
`pullbackFormsLinearMap`. Until then, no production declarations. -/
def reconStub : Unit := ()

end JacobianChallenge.Periods
