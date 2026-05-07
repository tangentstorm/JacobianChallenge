import Jacobian.HolomorphicForms.MeromorphicFunction

/-!
# Blueprint compatibility shim for `def:meromorphic-function`

The production-facing meromorphic-function structure has been promoted to
`Jacobian.HolomorphicForms.MeromorphicFunction`.
-/

namespace JacobianChallenge.Blueprint

export JacobianChallenge.HolomorphicForms (MeromorphicFunctionType)

end JacobianChallenge.Blueprint
