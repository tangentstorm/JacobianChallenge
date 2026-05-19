import Jacobian.HolomorphicForms.MeromorphicToCp1

/-!
# Blueprint compatibility shim for `def:meromorphic-to-cp1`

The production-facing CP¹ lift API has been promoted to
`Jacobian.HolomorphicForms.MeromorphicToCp1`.
-/

namespace JacobianChallenge.Blueprint

export JacobianChallenge.HolomorphicForms
  (meromorphicToCp1
   liftToCp1_continuous
   liftToCp1_holomorphicAt_finite
   liftToCp1_holomorphicAt_infty
   liftToCp1_holomorphicAt
   liftToCp1_local_kfold_ramified
   liftToCp1_weightedFiberSum_eventually_eq
   liftToCp1_isHolomorphic)

end JacobianChallenge.Blueprint
