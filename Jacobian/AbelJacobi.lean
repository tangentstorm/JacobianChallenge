import Jacobian.AbelJacobi.Defs
import Jacobian.AbelJacobi.Composition
import Jacobian.AbelJacobi.Smul
import Jacobian.AbelJacobi.BaseChange

/-!
# Abel-Jacobi infrastructure (witness skeleton)

Top-level module for Queue F. Currently only re-exports the
witness skeleton in `Defs`. The full path-integral construction is
deferred (multi-chart path integration + Stokes; see Inventory).

**Excluded on purpose:**
- `Recon` — name-discovery and design document; not part of the
  public API.
-/
