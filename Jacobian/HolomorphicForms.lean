import Jacobian.HolomorphicForms.AnalyticGenus
import Jacobian.HolomorphicForms.AnalyticGenusPos
import Jacobian.HolomorphicForms.ToFunApply
import Jacobian.HolomorphicForms.ToFunApplyVec
import Jacobian.HolomorphicForms.ToFunApplyVecExtra
import Jacobian.HolomorphicForms.EvalLinearMap
import Jacobian.HolomorphicForms.EvalLinearMapApi
import Jacobian.HolomorphicForms.EvalLinearMapZsmul
import Jacobian.HolomorphicForms.Ext
import Jacobian.HolomorphicForms.ExtEvalLinearMap
import Jacobian.HolomorphicForms.AnalyticGenusWitness
import Jacobian.HolomorphicForms.EvalLinearMapVec
import Jacobian.HolomorphicForms.EvalLinearMapVecExtra
import Jacobian.HolomorphicForms.CotangentBundle
import Jacobian.HolomorphicForms.Defs
import Jacobian.HolomorphicForms.FiniteDimensional

/-!
# Holomorphic forms infrastructure

Top-level module that re-exports the production Queue C target
files. Other modules can import `Jacobian.HolomorphicForms` instead
of pulling each sibling in by hand.

**Excluded on purpose:**
- `Recon` — name-discovery and design document; not part of the
  public API. The recon file still builds (it is a valid Lean
  module) and remains on disk, but it is not re-exported.
-/
