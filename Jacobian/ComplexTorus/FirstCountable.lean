import Mathlib.Topology.Algebra.Group.Quotient
import Jacobian.ComplexTorus.Defs

/-!
# First-countability and second-countability of the complex-torus quotient

`FirstCountableTopology` follows for free: any `NormedAddCommGroup V`
is a `PseudoMetricSpace`, hence first-countable, and Mathlib has
`QuotientAddGroup.instFirstCountableTopology`.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  (Λ : FullComplexLattice V)

/--
The complex-torus quotient is first countable (via the underlying
metric structure on `V`).
-/
instance firstCountableTopology_quotient :
    FirstCountableTopology (quotient V Λ) :=
  inferInstance

/--
The complex-torus quotient is second countable when the ambient
space is. The hypothesis is automatic for finite-dimensional `V`.
-/
instance secondCountableTopology_quotient
    [SecondCountableTopology V] :
    SecondCountableTopology (quotient V Λ) :=
  inferInstance

end JacobianChallenge.ComplexTorus
