import Jacobian.Periods.ChartBallAtPoint
import Jacobian.Periods.ChartedForm
import Jacobian.Periods.ChartedFormPullback
import Jacobian.Periods.ChartedFormSimp
import Jacobian.Periods.IntegralOneCycle
import Jacobian.Periods.LebesgueChartRadius
import Jacobian.Periods.PathIntegralChart
import Jacobian.Periods.PathIntegralChartCorrect
import Jacobian.Periods.PathIntegralChartCorrectSimp
import Jacobian.Periods.PathIntegralChartCorrectZero
import Jacobian.Periods.PathLift
import Jacobian.Periods.PathLiftSimp
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
