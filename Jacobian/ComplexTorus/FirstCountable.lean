import Mathlib.Topology.Algebra.Group.Quotient
import Jacobian.WorkPackets.StatementBank

/-!
# First-countability and second-countability of the complex-torus quotient

Queue B sibling of `Jacobian/ComplexTorus/Basic.lean`.

Both should follow directly from Mathlib's `QuotientAddGroup` instances:
the quotient of a first/second-countable additive topological group is
first/second-countable.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  (Λ : FullComplexLattice V)

/-- The complex-torus quotient is first countable. -/
instance firstCountableTopology_quotient :
    FirstCountableTopology (quotient V Λ) :=
  inferInstance

/-- The complex-torus quotient is second countable. -/
instance secondCountableTopology_quotient :
    SecondCountableTopology (quotient V Λ) :=
  inferInstance

end JacobianChallenge.ComplexTorus
