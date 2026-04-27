import Jacobian.AnalyticJacobian.Defs
import Jacobian.AnalyticJacobian.Mk
import Jacobian.AnalyticJacobian.MkOps
import Jacobian.AnalyticJacobian.MkExt
import Jacobian.AnalyticJacobian.MkMembership
import Jacobian.AnalyticJacobian.MkArith
import Jacobian.AnalyticJacobian.MkSubArith
import Jacobian.AnalyticJacobian.MkPeriodPairing
import Jacobian.AnalyticJacobian.MkPeriodPairingSmul
import Jacobian.AnalyticJacobian.MkPeriodPairingCycle
import Jacobian.AnalyticJacobian.MkPeriodPairingCycleSmul
import Jacobian.AnalyticJacobian.EvalJacobianClassEq
import Jacobian.AnalyticJacobian.EvalJacobianClassEqSubMem
import Jacobian.AnalyticJacobian.EvalJacobianClassPeriodPairing
import Jacobian.AnalyticJacobian.EvalJacobianClassMember
import Jacobian.AnalyticJacobian.EvalJacobianClass
import Jacobian.AnalyticJacobian.EvalJacobianClassOps
import Jacobian.AnalyticJacobian.EvalJacobianClassSmul
import Jacobian.AnalyticJacobian.EvalJacobianClassZero
import Jacobian.AnalyticJacobian.EvalJacobianClassMkBridge
import Jacobian.AnalyticJacobian.NontrivialWitness

/-!
# Analytic Jacobian infrastructure

Top-level module that re-exports the production Queue E target
files. Currently a single file (`Defs`) defining
`AnalyticJacobianGroup E X` as the abstract group quotient
`(HolomorphicOneForm E X →ₗ[ℂ] ℂ) ⧸ periodSubgroup E X`.

The full Lie-group structure (topology, manifold, compact-torus
instances) is layered on top of this base via the deferred
full-lattice property of `periodSubgroup`.
-/
