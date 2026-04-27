import Jacobian.TraceDegree.PullbackFormsLinearMap
import Jacobian.TraceDegree.PullbackFormsLinearMapApply
import Jacobian.TraceDegree.PullbackFormsLinearMapApplyLinear
import Jacobian.TraceDegree.PullbackFormsLinearMapApplyApplyLinear
import Jacobian.TraceDegree.PullbackFormsLinearMapConst
import Jacobian.TraceDegree.PullbackFormsLinearMapConstApplyVec
import Jacobian.TraceDegree.PullbackFormsLinearMapId
import Jacobian.TraceDegree.PullbackFormsLinearMapIdApplyVec
import Jacobian.TraceDegree.PullbackFormsLinearMapSimp
import Jacobian.TraceDegree.PullbackFormsLinearMapSmul
import Jacobian.TraceDegree.PullbackFun
import Jacobian.TraceDegree.PullbackFunAddSubApply
import Jacobian.TraceDegree.PullbackFunApply
import Jacobian.TraceDegree.PullbackFunApplyVec
import Jacobian.TraceDegree.PullbackFunComp
import Jacobian.TraceDegree.PullbackFunCompApply
import Jacobian.TraceDegree.PullbackFunCompId
import Jacobian.TraceDegree.PullbackFormsLinearMapCompId
import Jacobian.TraceDegree.PullbackFormsLinearMapCompIdApply
import Jacobian.TraceDegree.PullbackFormsLinearMapComp
import Jacobian.TraceDegree.PullbackFunCompConst
import Jacobian.TraceDegree.PullbackFunCompConstApply
import Jacobian.TraceDegree.PullbackFunConstComp
import Jacobian.TraceDegree.PullbackFunConstCompConst
import Jacobian.TraceDegree.PullbackFunConstCompConstBundled
import Jacobian.TraceDegree.PullbackFunMixedConstIdApply
import Jacobian.TraceDegree.PullbackFormsLinearMapMixedConstId
import Jacobian.TraceDegree.PullbackFunIdComposeId
import Jacobian.TraceDegree.PullbackFunEvalLinearMap
import Jacobian.TraceDegree.PullbackFunIdEval
import Jacobian.TraceDegree.PullbackFunIdEvalDist
import Jacobian.TraceDegree.PullbackFunIdEvalSmul
import Jacobian.TraceDegree.PullbackFunIdEvalVec
import Jacobian.TraceDegree.PullbackFunIdEvalVecExtra
import Jacobian.TraceDegree.PullbackFormsLinearMapIdEval
import Jacobian.TraceDegree.PullbackFormsLinearMapIdEvalVec
import Jacobian.TraceDegree.PullbackFormsLinearMapIdEvalVecExtra
import Jacobian.TraceDegree.PullbackFormsLinearMapIdEvalDist
import Jacobian.TraceDegree.PullbackFormsLinearMapIdEvalSmul
import Jacobian.TraceDegree.PullbackFormsLinearMapCompConst
import Jacobian.TraceDegree.PullbackFormsLinearMapCompConstApplyVec
import Jacobian.TraceDegree.PullbackFunConst
import Jacobian.TraceDegree.PullbackFunConstApplyVec
import Jacobian.TraceDegree.PullbackFunId
import Jacobian.TraceDegree.PullbackFunIdApply
import Jacobian.TraceDegree.PullbackFunIdApplyVec
import Jacobian.TraceDegree.PullbackFunSimpApply
import Jacobian.TraceDegree.PullbackFunSimpApplyVec
import Jacobian.TraceDegree.PullbackFunSmul
import Jacobian.TraceDegree.PullbackFunSub

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
