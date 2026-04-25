import Mathlib.Topology.Algebra.Group.Quotient
import Jacobian.ComplexTorus.Defs

/-!
# First-countability and second-countability of the complex-torus quotient

Queue B sibling of `Jacobian/ComplexTorus/Basic.lean`.

`FirstCountableTopology` follows for free: any `NormedAddCommGroup V`
is a `PseudoMetricSpace`, hence first-countable, and Mathlib has
`QuotientAddGroup.instFirstCountableTopology`.

`SecondCountableTopology` does **not** follow for free: an arbitrary
normed complex vector space need not be second-countable (e.g. an
uncountable-dimensional Hilbert space). The instance below requires
`SecondCountableTopology V` as an explicit hypothesis. For our intended
use case — finite-dimensional complex vector spaces — the hypothesis is
discharged automatically because finite-dim normed spaces are separable
metric spaces.
-/

namespace JacobianChallenge.ComplexTorus

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  (Λ : FullComplexLattice V)

/-- The complex-torus quotient is first countable (via the underlying
metric structure on `V`). -/
instance firstCountableTopology_quotient :
    FirstCountableTopology (quotient V Λ) :=
  inferInstance

/-- The complex-torus quotient is second countable when the ambient
space is. The hypothesis is automatic for finite-dimensional `V`. -/
instance secondCountableTopology_quotient
    [SecondCountableTopology V] :
    SecondCountableTopology (quotient V Λ) :=
  inferInstance

end JacobianChallenge.ComplexTorus
