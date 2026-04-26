import Jacobian.TraceDegree.PullbackFun

/-!
# Trace, degree, pushforward, pullback infrastructure

Top-level module that re-exports the production Queue G target
files.

**Excluded on purpose:**
- `Recon` — name-discovery and design document; not part of the
  public API. The recon file still builds and remains on disk, but
  it is not re-exported.

**Notes:**
- `PullbackFun` defines `pullbackFormsFun` (the chain-rule pullback
  at the function level) plus zero/neg/add linearity. The smoothness
  upgrade to `HolomorphicOneForm E X` is intentionally a follow-up.
-/
