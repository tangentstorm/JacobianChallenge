import Jacobian.Periods.ChartBallAtPoint
import Jacobian.Periods.ChartLiftApply
import Jacobian.Periods.ChartLiftReflSubpath
import Jacobian.Periods.DivFinIcc
import Jacobian.Periods.ChartedForm
import Jacobian.Periods.ChartedFormSmul
import Jacobian.Periods.ChartedFormPullback
import Jacobian.Periods.ChartedFormPullbackApply
import Jacobian.Periods.ChartedFormPullbackLinearMap
import Jacobian.Periods.ChartedFormPullbackLinearMapApply
import Jacobian.Periods.ChartedFormPullbackLinearMapSimp
import Jacobian.Periods.ChartedFormPullbackLinearMapSmul
import Jacobian.Periods.ChartedFormPullbackSimp
import Jacobian.Periods.ChartedFormPullbackSmul
import Jacobian.Periods.ChartedFormPullbackSub
import Jacobian.Periods.ChartedFormPullbackCurveIntegrable
import Jacobian.Periods.ChartedFormSimp
import Jacobian.Periods.IntegralOneCycle
import Jacobian.Periods.LebesgueChartRadius
import Jacobian.Periods.PathIntegralChart
import Jacobian.Periods.PathIntegralChartCorrect
import Jacobian.Periods.PathIntegralChartCorrectApply
import Jacobian.Periods.PathIntegralChartCorrectAdd
import Jacobian.Periods.PathIntegralChartCorrectLinear
import Jacobian.Periods.PathIntegralChartCorrectSmul
import Jacobian.Periods.PathIntegralChartCorrectSimp
import Jacobian.Periods.PathIntegralChartCorrectZero
import Jacobian.Periods.PathIntegralViaChartCorrect
import Jacobian.Periods.PathIntegralViaChartCorrectAdd
import Jacobian.Periods.PathIntegralViaChartCorrectApply
import Jacobian.Periods.PathIntegralViaChartCorrectNeg
import Jacobian.Periods.PathIntegralViaChartCorrectSmul
import Jacobian.Periods.PathIntegralViaChartCorrectZero
import Jacobian.Periods.PathIntegralViaCover
import Jacobian.Periods.PathIntegralViaCoverNeg
import Jacobian.Periods.PathIntegralViaCoverWithApply
import Jacobian.Periods.PathIntegralViaCoverPick
import Jacobian.Periods.PathIntegralViaCoverPickApply
import Jacobian.Periods.PathIntegralViaCoverPickRefl
import Jacobian.Periods.PathIntegralViaCoverPickSimp
import Jacobian.Periods.PathIntegralViaCoverPickSmul
import Jacobian.Periods.PathIntegralViaCoverWithRefl
import Jacobian.Periods.PathIntegralViaCoverSmul
import Jacobian.Periods.PathIntegralViaCoverZero
import Jacobian.Periods.PathLift
import Jacobian.Periods.PathLiftSimp
import Jacobian.Periods.PathLiftSimpFromX
import Jacobian.Periods.PathReflSubpath
import Jacobian.Periods.PathPartition
import Jacobian.Periods.PeriodFunctional

/-!
# Periods infrastructure

Top-level module that re-exports the production Queue D target
files. Other modules can import `Jacobian.Periods` instead of
pulling each sibling in by hand.

**Excluded on purpose:**
- `Recon` — name-discovery and design document; not part of the
  public API. The recon file still builds and remains on disk, but
  it is not re-exported.

**Notes:**
- `PeriodFunctional` carries one `opaque periodPairing` whose
  implementation is deferred (multi-chart path integration + Stokes
  on manifolds). All other modules are sorry-free.
-/
